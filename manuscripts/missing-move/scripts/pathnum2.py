"""Scalable exact path-partition feasibility via CP-SAT circuit constraints.

decompose(G, k, ...) decides whether E(G) partitions into at most k simple paths
satisfying endpoint constraints.  Each colour c (one per potential path) is
modelled as a circuit through a dummy node d_c over V(G) + {d_c}: arcs u->v along
edges of colour c, d_c->v (path start), v->d_c (path end), self-loops for
vertices not on the path (and for d_c when the colour is unused).  AddCircuit
forces each colour class to be a single simple path (or empty).  No path
enumeration, so dense graphs on 12-16 vertices are feasible.

Endpoint counts: b(v) = sum_c [start_c(v)] + [end_c(v)].
"""
from __future__ import annotations

from typing import Dict, List, Optional, Tuple

import networkx as nx
from ortools.sat.python import cp_model


def decompose(G: nx.Graph, k: int, *, exact_ends: Optional[Dict] = None,
              min_ends: Optional[Dict] = None, max_ends: Optional[Dict] = None,
              time_limit: float = 120.0, workers: int = 4, hint=None):
    nodes = list(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    n = len(nodes)
    edges = list(G.edges())
    model = cp_model.CpModel()
    x = {}  # x[e, c]
    start = {}
    end = {}
    for c in range(k):
        d = n  # dummy node index
        arcs = []
        used = model.NewBoolVar(f"used{c}")
        arcs.append((d, d, used.Not()))
        inpath = []
        for v in nodes:
            i = idx[v]
            s = model.NewBoolVar(f"s{c}_{i}")
            t = model.NewBoolVar(f"t{c}_{i}")
            start[c, v] = s
            end[c, v] = t
            model.AddBoolOr([s.Not(), t.Not()])  # no one-vertex path
            arcs.append((d, i, s))
            arcs.append((i, d, t))
            onp = model.NewBoolVar(f"on{c}_{i}")
            arcs.append((i, i, onp.Not()))
            inpath.append(onp)
        for j, (u, v) in enumerate(edges):
            a = model.NewBoolVar(f"a{c}_{j}")
            b = model.NewBoolVar(f"b{c}_{j}")
            arcs.append((idx[u], idx[v], a))
            arcs.append((idx[v], idx[u], b))
            e = model.NewBoolVar(f"x{c}_{j}")
            model.Add(a + b == e)
            x[j, c] = e
        model.AddCircuit(arcs)
        # used iff some vertex on path
        model.AddMaxEquality(used, inpath)
        if c > 0:
            model.AddImplication(used, usedprev)
        usedprev = used
    for j in range(len(edges)):
        model.AddExactlyOne(x[j, c] for c in range(k))
    endsum = {}
    for v in nodes:
        endsum[v] = sum(start[c, v] + end[c, v] for c in range(k))
    for dct, op in ((exact_ends, "=="), (min_ends, ">="), (max_ends, "<=")):
        if not dct:
            continue
        for v, val in dct.items():
            if op == "==":
                model.Add(endsum[v] == val)
            elif op == ">=":
                model.Add(endsum[v] >= val)
            else:
                model.Add(endsum[v] <= val)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = workers
    st = solver.Solve(model)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return solver.StatusName(st), None
    # extract paths
    paths = []
    for c in range(k):
        es = [edges[j] for j in range(len(edges)) if solver.Value(x[j, c])]
        if not es:
            continue
        H = nx.Graph(es)
        s = [v for v in H if H.degree(v) == 1]
        P = nx.shortest_path(H, s[0], s[1])
        paths.append(tuple(P))
    return solver.StatusName(st), paths


if __name__ == "__main__":
    import random
    from pathnum import solve, verify_partition
    rng = random.Random(3)
    bad = 0
    for t in range(int(__import__("sys").argv[1]) if len(__import__("sys").argv) > 1 else 60):
        n = rng.randint(4, 8)
        m = rng.randint(n - 1, n * (n - 1) // 2)
        G = nx.gnm_random_graph(n, m, seed=rng.randrange(10**6))
        if not nx.is_connected(G):
            continue
        p = solve(G).value
        st, P = decompose(G, p)
        st2, P2 = decompose(G, p - 1) if p > 1 else ("INFEASIBLE", None)
        ok = P is not None and verify_partition(G, P) and len(P) <= p and P2 is None
        # endpoint-constrained cross-check
        E = [v for v in G if G.degree(v) % 2 == 0]
        if E:
            r = E[0]
            a = solve(G, budget=n // 2, min_ends={r: 2}).status in ("OPTIMAL", "FEASIBLE")
            b = decompose(G, n // 2, min_ends={r: 2})[1] is not None
            ok &= (a == b)
        bad += not ok
        if not ok:
            print("MISMATCH", sorted(G.edges()), p, st, st2)
    print("cross-check mismatches:", bad)

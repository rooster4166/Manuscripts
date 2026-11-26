"""Exchange structure of endpoint vectors of path decompositions.

For a graph G and an integer k let J_k(G) be the set of endpoint vectors b
(b(v) = number of path ends at v) over all decompositions of E(G) into exactly
k simple paths.  Parity forces b(v) = (d(v) mod 2) + 2 c(v); write C_k(G) for
the set of halved vectors c.  Every c in C_k has the same sum k - #odd/2.

Conjecture under test (M-convexity): C_k(G) is an M-convex set, i.e. for
x, y in C_k and u with x(u) > y(u) there is v with x(v) < y(v) such that
x - e_u + e_v and y + e_u - e_v both lie in C_k.
"""

from __future__ import annotations

import itertools
import sys
from typing import Dict, List, Set, Tuple

import networkx as nx
from ortools.sat.python import cp_model

from pathnum import edge_index, enumerate_paths, path_number


def endpoint_vectors(G: nx.Graph, k: int, cap: int = 100000) -> Set[Tuple[int, ...]]:
    """All endpoint vectors (ordered by sorted node list) of k-path decompositions."""
    nodes = sorted(G.nodes())
    paths = enumerate_paths(G)
    eidx = edge_index(G)
    m = len(eidx)
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f"x{i}") for i in range(len(paths))]
    by_edge = [[] for _ in range(m)]
    for i, P in enumerate(paths):
        mk = P.mask
        while mk:
            low = mk & -mk
            by_edge[low.bit_length() - 1].append(i)
            mk ^= low
    for e in range(m):
        model.AddExactlyOne(x[i] for i in by_edge[e])
    model.Add(sum(x) == k)
    ends = {v: [] for v in nodes}
    for i, P in enumerate(paths):
        a, b = P.ends
        ends[a].append(i)
        ends[b].append(i)
    ev = {}
    for v in nodes:
        ev[v] = model.NewIntVar(0, G.degree(v), f"e{v}")
        model.Add(ev[v] == sum(x[i] for i in ends[v]))
    found: Set[Tuple[int, ...]] = set()
    solver = cp_model.CpSolver()
    solver.parameters.num_workers = 4
    solver.parameters.max_time_in_seconds = 60
    while len(found) < cap:
        st = solver.Solve(model)
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            break
        vec = tuple(solver.Value(ev[v]) for v in nodes)
        found.add(vec)
        lits = []
        for v, val in zip(nodes, vec):
            bvar = model.NewBoolVar("")
            model.Add(ev[v] != val).OnlyEnforceIf(bvar)
            lits.append(bvar)
        model.AddBoolOr(lits)
    return found


def halve(G: nx.Graph, vecs: Set[Tuple[int, ...]]) -> Set[Tuple[int, ...]]:
    nodes = sorted(G.nodes())
    par = [G.degree(v) % 2 for v in nodes]
    return {tuple((b - p) // 2 for b, p in zip(vec, par)) for vec in vecs}


def m_convex_violation(C: Set[Tuple[int, ...]]):
    """Return a violating (x, y, u) or None."""
    if not C:
        return None
    n = len(next(iter(C)))
    for x in C:
        for y in C:
            if x == y:
                continue
            for u in range(n):
                if x[u] <= y[u]:
                    continue
                ok = False
                for v in range(n):
                    if x[v] >= y[v]:
                        continue
                    x2 = list(x); x2[u] -= 1; x2[v] += 1
                    y2 = list(y); y2[u] += 1; y2[v] -= 1
                    if tuple(x2) in C and tuple(y2) in C:
                        ok = True
                        break
                if not ok:
                    return (x, y, u)
    return None


def main(nmax: int, extra: int):
    from networkx.generators.atlas import graph_atlas_g

    stats = {}
    bad = []
    for G in graph_atlas_g():
        n = G.number_of_nodes()
        if n < 2 or n > nmax or G.number_of_edges() == 0 or not nx.is_connected(G):
            continue
        p = path_number(G)
        for k in range(p, p + extra + 1):
            vecs = endpoint_vectors(G, k)
            if not vecs:
                continue
            C = halve(G, vecs)
            viol = m_convex_violation(C)
            key = (n, k - p)
            s = stats.setdefault(key, [0, 0])
            s[0 if viol is None else 1] += 1
            if viol is not None:
                bad.append((n, k, p, sorted(G.edges()), viol, len(C)))
    for key in sorted(stats):
        print(f"n={key[0]} k=p+{key[1]}: M-convex {stats[key][0]}, violations {stats[key][1]}")
    for b in bad[:40]:
        print("VIOLATION", b)


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    extra = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    main(nmax, extra)

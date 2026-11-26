"""Test the complementary-pair property CP(G) on small graphs.

CP(G): there are two path decompositions D1, D2 of G such that every odd vertex
is an end exactly once in each, and every even vertex of positive degree is an
end exactly twice in one of them and zero times in the other.

Counting ends, |D1| + |D2| = n' (number of non-isolated vertices), so CP(G)
implies p(G) <= floor(n'/2).  Odd semi-cliques violate the floor, hence CP.
"""

from __future__ import annotations

import sys
from typing import Optional

import networkx as nx
from ortools.sat.python import cp_model

from pathnum import enumerate_paths, edge_index


def cp_pair(G: nx.Graph, time_limit: float = 60.0, fixed_side=None):
    """Return (status, (D1, D2)) for the complementary-pair problem.

    fixed_side: optional dict v -> 0/1 forcing even vertex v to be doubled in
    D1 (1) or D2 (0).
    """
    paths = enumerate_paths(G)
    eidx = edge_index(G)
    m = len(eidx)
    model = cp_model.CpModel()
    xs = []
    for side in (0, 1):
        x = [model.NewBoolVar(f"x{side}_{i}") for i in range(len(paths))]
        xs.append(x)
        by_edge = [[] for _ in range(m)]
        for i, P in enumerate(paths):
            mk = P.mask
            while mk:
                low = mk & -mk
                by_edge[low.bit_length() - 1].append(i)
                mk ^= low
        for e in range(m):
            model.AddExactlyOne(x[i] for i in by_edge[e])
    ends_at = {v: [] for v in G.nodes()}
    for i, P in enumerate(paths):
        a, b = P.ends
        ends_at[a].append(i)
        ends_at[b].append(i)
    for v in G.nodes():
        d = G.degree(v)
        if d == 0:
            continue
        s0 = sum(xs[0][i] for i in ends_at[v])
        s1 = sum(xs[1][i] for i in ends_at[v])
        if d % 2:
            model.Add(s0 == 1)
            model.Add(s1 == 1)
        else:
            y = model.NewBoolVar(f"y{v}")
            model.Add(s0 == 2 * y)
            model.Add(s1 == 2 - 2 * y)
            if fixed_side and v in fixed_side:
                model.Add(y == fixed_side[v])
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = 4
    st = solver.Solve(model)
    name = solver.StatusName(st)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        D = [[paths[i].verts for i in range(len(paths)) if solver.Value(xs[s][i])] for s in (0, 1)]
        return name, D
    return name, None


def is_odd_semi_clique(G: nx.Graph) -> bool:
    n = G.number_of_nodes()
    if n % 2 == 0:
        return False
    k = n // 2
    return n * (n - 1) // 2 - G.number_of_edges() <= k - 1


def main(nmax: int):
    from networkx.generators.atlas import graph_atlas_g

    counts = {}
    failures = []
    for G in graph_atlas_g():
        n = G.number_of_nodes()
        if n < 2 or n > nmax or G.number_of_edges() == 0 or not nx.is_connected(G):
            continue
        st, D = cp_pair(G)
        ok = D is not None
        key = (n, ok)
        counts[key] = counts.get(key, 0) + 1
        if not ok:
            failures.append((n, G.number_of_edges(), is_odd_semi_clique(G), sorted(G.edges()), st))
    for n in range(2, nmax + 1):
        print(f"n={n}: CP holds {counts.get((n, True), 0)}, fails {counts.get((n, False), 0)}")
    print("failures (n, m, odd_semi_clique?, edges, status):")
    for f in failures:
        print(f)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 7)

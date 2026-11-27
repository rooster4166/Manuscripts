#!/usr/bin/env python3
"""Audit A13: the merged manuscript's claim that at orders 6 and 8 every half-set of a connected
graph of minimum degree >= 3 is cut-feasible (Table 1 rows 'of which delta >= 3': 13 graphs /
60 half-sets at order 6, 2,475 / 19,422 at order 8, none excluded)."""
import itertools
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a13_check as C  # noqa: E402

for path in ('data/conn6.g6', 'data/conn8.g6'):
    g = hs = bad = 0
    for line in open(path):
        G = nx.from_graph6_bytes(line.strip().encode())
        n = G.number_of_nodes()
        deg = [G.degree(v) for v in range(n)]
        if min(deg) < 3:
            continue
        Ev = [v for v in range(n) if deg[v] % 2 == 0]
        if not Ev:
            continue
        g += 1
        cd = C.CutData(G)
        for M in itertools.combinations(Ev, len(Ev) // 2):
            hs += 1
            bad += cd.profile_ok(C.simple_profile(deg, set(M))) is not None
    print(path, 'delta>=3, e>0: graphs', g, 'half-sets', hs, 'cut-infeasible', bad)

#!/usr/bin/env python3
"""Audit A13: independent check of the order-18 EMM_3 counterexample (synthesis §14,
scripts/emm3_counterexample.py): the graph is rebuilt from the description, the half-set
M = V(K_{4,4}) is tested against ED (1) by brute force over all v and W (2^18 subsets), and
realisability is decided by the A13 DFS oracle."""
import itertools
import os
import sys
import time

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a13_check as C  # noqa: E402
from a13_realis import realisable  # noqa: E402

a0, a1, a2, a3, b0, b1, b2, b3, p, q = range(10)
G = nx.Graph()
G.add_edges_from(itertools.combinations([a0, a1, a2, a3], 2))
G.add_edges_from(itertools.combinations([b0, b1, b2, b3], 2))
G.add_edges_from([(p, a1), (p, a2), (p, b1), (q, a3), (q, b2), (q, b3)])
S = list(range(10, 18))
G.add_edges_from((x, y) for x in S[:4] for y in S[4:])
G.add_edges_from([(10, p), (10, b0)])
n = G.number_of_nodes()
deg = [G.degree(v) for v in range(n)]
Ev = [v for v in range(n) if deg[v] % 2 == 0]
print('n', n, 'm', G.number_of_edges(), 'min degree', min(deg), 'e', len(Ev), 'connected', nx.is_connected(G))
M = set(S)
assert M <= set(Ev) and 2 * len(M) == len(Ev)
b = C.simple_profile(deg, M)
cd = C.CutData(G)
print('M = V(K44) satisfies (1) at every v, W:', cd.profile_ok(b) is None)
t = time.time()
print('realisable:', realisable(G, b), '[%.0fs]' % (time.time() - t))

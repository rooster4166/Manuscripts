#!/usr/bin/env python3
"""Classify irreducible PC instances (lines 'STUCK[_TWIN] g6 b=...' from stuck.c) by twin status,
adjacency of the zeros, |N(u) - v|, minimality of the profile (b = m_Z), and, for the twin minimal ones,
the number of even vertices of the graph.   Usage: grep STUCK data/irreducible.txt | python3 classify_irred.py"""
import sys
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from wcheck31 import g6
C = Counter(); ev = Counter()
for l in sys.stdin:
    f = l.split()
    if not f or not f[0].startswith('STUCK'):
        continue
    tw = f[0] == 'STUCK_TWIN'; n, E = g6(f[1]); b = [int(t) for t in f[2][2:].split(',')]
    adj = {i: set() for i in range(n)}
    for i, j in E:
        adj[i].add(j); adj[j].add(i)
    u, v = [i for i in range(n) if b[i] == 0]
    minimal = all(b[i] == (1 if len(adj[i]) % 2 else (0 if i in (u, v) else 2)) for i in range(n))
    C[(n, 'twin' if tw else 'non-twin', 'u~v' if v in adj[u] else 'u!~v', len(adj[u] - {v}),
       'minimal' if minimal else 'non-minimal')] += 1
    if tw and minimal:
        ev[(n, sum(1 for i in range(n) if len(adj[i]) % 2 == 0))] += 1
for k in sorted(C):
    print(k, C[k])
print('twin minimal, by (order, number of even vertices):', dict(sorted(ev.items())))

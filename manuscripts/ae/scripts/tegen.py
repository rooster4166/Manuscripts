"""tegen.py -- terminal-edge queries TE(L, g, x) (ae session).

L (stdin, graph6) with at most one vertex of positive even degree; g odd with d(g) >= 3; x a
neighbour of g.  Query: some Lovasz decomposition of L has gx as the terminal edge at g, i.e.
'T g y' for every other neighbour y of g.  argv[1]: 'all' (every such (g, x)), 'even' (only x the
even vertex: equivalent to AE for K = L - gx), 'odd' (only x odd)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
from lnlib import g6_decode
mode = sys.argv[1]
for line in sys.stdin:
    g6 = line.strip()
    if not g6: continue
    n, adj = g6_decode(g6)
    ev = [v for v in range(n) if adj[v] and len(adj[v]) % 2 == 0]
    if len(ev) > 1: continue
    for g in range(n):
        if len(adj[g]) % 2 == 0 or len(adj[g]) < 3: continue
        for x in sorted(adj[g]):
            xe = len(adj[x]) % 2 == 0
            if mode == 'even' and not xe: continue
            if mode == 'odd' and xe: continue
            print(g6 + ''.join(f' T {g} {y}' for y in sorted(adj[g]) if y != x))

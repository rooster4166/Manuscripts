"""aegen.py -- AE queries: every graph (stdin, graph6) with exactly one vertex g of positive even
degree, and every odd c != g with c not adjacent to g and c in the component of g: 'A c g'."""
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
for line in sys.stdin:
    g6 = line.strip(); n, adj = g6_decode(g6)
    ev = [v for v in range(n) if adj[v] and len(adj[v]) % 2 == 0]
    if len(ev) != 1: continue
    g = ev[0]
    seen = {g}; st = [g]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen: seen.add(v); st.append(v)
    for c in sorted(seen):
        if c != g and c not in adj[g] and len(adj[c]) % 2 == 1:
            print(g6, 'A', c, g)

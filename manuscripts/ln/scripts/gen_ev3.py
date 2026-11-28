"""graphs whose vertices of positive even degree are pairwise at distance >= 3 (at least 2 of them)"""
import sys
from lnlib import g6_decode
for line in sys.stdin:
    g = line.strip()
    n, adj = g6_decode(g)
    ev = [v for v in range(n) if adj[v] and len(adj[v]) % 2 == 0]
    if len(ev) < 2: continue
    ok = True
    for i in range(len(ev)):
        for j in range(i+1, len(ev)):
            a, b = ev[i], ev[j]
            if b in adj[a] or adj[a] & adj[b]: ok = False
    if ok: print(g)

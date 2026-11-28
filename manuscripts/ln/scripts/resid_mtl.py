"""filter MTL instances (lnsolve lines with S c x) to the Case I.2 residual: the even vertex g has
all its neighbours in X (avoided vertices) or L (tail leaves); print with the local structure."""
import sys
from lnlib import g6_decode
for line in sys.stdin:
    t = line.split()
    n, adj = g6_decode(t[0])
    deg = [len(a) for a in adj]
    ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
    if not ev: continue
    g = ev[0]
    X = set(); L = set()
    for i in range(1, len(t), 3):
        L.add(int(t[i + 1])); X.add(int(t[i + 2]))
    if adj[g] <= X | L:
        print(line.strip(), '| g', g, 'deg', deg[g], 'N(g)', sorted(adj[g]), 'triangle' if any(b in adj[a] for a in adj[g] for b in adj[g]) else '')

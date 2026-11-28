"""find MTL2 (singleton) instances in the (R1) residual: token g, deg 2, N(g) = {x1, x2}; classify a/b/ii/iii"""
import sys
from lnlib import g6_decode
for line in sys.stdin:
    t = line.split()
    n, adj = g6_decode(t[0])
    deg = [len(a) for a in adj]
    ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
    if not ev: continue
    g = ev[0]
    c1, x1, c2, x2 = int(t[2]), int(t[3]), int(t[5]), int(t[6])
    w1, w2 = next(iter(adj[c1])), next(iter(adj[c2]))
    if g in (w1, w2) or adj[g] != {x1, x2} or x1 == x2: continue
    if x2 in adj[x1]: typ = 'R1b'
    elif w1 == x2 and w2 == x1: typ = 'R1a-iii'
    elif w1 == x2 or w2 == x1: typ = 'R1a-ii'
    else: typ = 'R1a-i'
    print(typ, line.strip())

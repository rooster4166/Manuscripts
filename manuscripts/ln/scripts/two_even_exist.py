import sys
from lnlib import g6_decode
for line in sys.stdin:
    g = line.strip()
    n, adj = g6_decode(g)
    deg = [len(a) for a in adj]
    ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
    if len(ev) == 2: print(g)

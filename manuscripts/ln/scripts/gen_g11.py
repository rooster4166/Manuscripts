"""gen_g11.py -- one leaf tail (l at w avoiding x; x not in {l,w}, x !~ w) plus one general tail
(c avoiding a; c odd, a not in N[c], c != l) in a graph with <= 1 even vertex g.
flags: 'loc' requires a not in N(g); 'gw' only instances with g = w; 'gnw' only g != w (or no g)."""
import sys
from lnlib import g6_decode
flags = set(sys.argv[1:])
for line in sys.stdin:
    gs = line.strip()
    if not gs: continue
    n, adj = g6_decode(gs)
    deg = [len(a) for a in adj]
    ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
    if len(ev) > 1: continue
    g = ev[0] if ev else None
    leaves = [v for v in range(n) if deg[v] == 1]
    for l in leaves:
        w = next(iter(adj[l]))
        if 'gw' in flags and g != w: continue
        if 'gnw' in flags and g == w: continue
        for x in range(n):
            if x in (l, w) or x in adj[w]: continue
            for c in range(n):
                if deg[c] % 2 == 0 or c in (l, x): continue
                for a in range(n):
                    if a == c or a in adj[c] or a == l: continue
                    if 'xa' not in flags and a == x: continue
                    if 'loc' in flags and g is not None and a in adj[g]: continue
                    print(gs, 'S', l, x, 'A', c, a)

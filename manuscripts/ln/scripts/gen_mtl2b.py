"""gen_mtl2b.py -- relaxed MTL2 instances: <=1 even vertex, two leaf tails (c_i at w_i avoiding x_i),
x_i != c_i, w_i; c_1 != c_2.  Flags (argv): 'noTS' drops (TS) (x_j may be w_i or c_i);
'adjok' allows x_i ~ w_i; 'evenx' allows x_i even."""
import sys
from lnlib import g6_decode
flags = set(sys.argv[1:])
for line in sys.stdin:
    g = line.strip()
    if not g: continue
    n, adj = g6_decode(g)
    deg = [len(a) for a in adj]
    ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
    if len(ev) > 1: continue
    leaves = [v for v in range(n) if deg[v] == 1]
    for i1, c1 in enumerate(leaves):
        w1 = next(iter(adj[c1]))
        for c2 in leaves[i1 + 1:]:
            w2 = next(iter(adj[c2]))
            if w1 == c2: continue
            for x1 in range(n):
                if x1 in (c1, w1): continue
                if 'adjok' not in flags and x1 in adj[w1]: continue
                if 'evenx' not in flags and deg[x1] % 2 == 0: continue
                if 'noTS' not in flags and x1 in (c2, w2): continue
                for x2 in range(n):
                    if x2 in (c2, w2): continue
                    if 'adjok' not in flags and x2 in adj[w2]: continue
                    if 'evenx' not in flags and deg[x2] % 2 == 0: continue
                    if 'noTS' not in flags and (x2 in (c1, w1) or x2 == x1): continue
                    print(g, 'S', c1, x1, 'S', c2, x2)

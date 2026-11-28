"""gen_mtl2.py -- instances of MTL2: <=1 vertex of positive even degree, two leaf tails
(c_i a leaf at w_i, x_i odd, x_i not in {c_i, w_i}, x_i not adjacent to w_i), with the static
condition (TS): c_j, x_j not in {c_i, w_i} for i != j, and x_1 != x_2.
reads graph6 on stdin, writes lnsolve lines with S c_i x_i (separation of the leaf from x_i)."""
import sys
from lnlib import g6_decode
for line in sys.stdin:
    g = line.strip()
    if not g: continue
    n, adj = g6_decode(g)
    deg = [len(a) for a in adj]
    ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
    if len(ev) > 1: continue
    leaves = [v for v in range(n) if deg[v] == 1]
    odd = [v for v in range(n) if deg[v] % 2 == 1]
    for i1, c1 in enumerate(leaves):
        w1 = next(iter(adj[c1]))
        for c2 in leaves[i1 + 1:]:
            w2 = next(iter(adj[c2]))
            if c2 in (c1, w1) or c1 in (c2, w2): continue
            for x1 in odd:
                if x1 in (c1, w1) or x1 in adj[w1] or x1 in (c2, w2): continue
                for x2 in odd:
                    if x2 in (c2, w2) or x2 in adj[w2] or x2 in (c1, w1) or x2 == x1: continue
                    print(g, 'S', c1, x1, 'S', c2, x2)

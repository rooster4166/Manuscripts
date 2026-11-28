"""gen_ln2.py -- L_N(2) instances: connected all-odd F, disjoint non-adjacent ordered pairs
(c1,a1),(c2,a2), up to the symmetry swapping the two pairs.  Output 'g6 c1 a1 c2 a2'."""
import sys
from lnlib import g6_decode
for line in sys.stdin:
    g = line.strip()
    n, adj = g6_decode(g)
    if any(len(a) % 2 == 0 for a in adj): continue
    P = [(c, a) for c in range(n) for a in range(n) if c != a and a not in adj[c]]
    for i, (c1, a1) in enumerate(P):
        for (c2, a2) in P[i + 1:]:
            if len({c1, a1, c2, a2}) == 4:
                print(g, c1, a1, c2, a2)

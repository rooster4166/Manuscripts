"""gen_inst.py -- own L_N(2) instance generator: connected graphs (stdin, graph6) with all degrees
odd; unordered pairs {(c1,a1),(c2,a2)} of ordered pairs with c_i !~ a_i and c1,a1,c2,a2 distinct.
Prints 'g6 c1 a1 c2 a2' with (c1,a1) < (c2,a2) lexicographically; summary on stderr."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a40lib import dec
ng = ni = 0
for g in sys.stdin:
    g = g.strip()
    if not g: continue
    n, A = dec(g)
    if any(len(a) % 2 == 0 for a in A): continue
    ng += 1
    pairs = sorted((c, a) for c in range(n) for a in range(n) if a != c and a not in A[c])
    for i, p in enumerate(pairs):
        for q in pairs[i + 1:]:
            if len({p[0], p[1], q[0], q[1]}) == 4:
                ni += 1
                print(g, p[0], p[1], q[0], q[1])
print('graphs', ng, 'instances', ni, file=sys.stderr)

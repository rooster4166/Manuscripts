#!/usr/bin/env python3
"""Independent check of jcert witness lines: g6 P Q1 ... Qk J=c1,a1,c2,a2.
P is a c1-c2 path avoiding a1, a2; {P, Q1..Qk} is a path decomposition of F with
exactly one end at every vertex (a Lovasz decomposition of the all-odd F) and
Q(c1) = Q(c2) = P.  Shares no code with the C solvers (own graph6 decoder)."""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from wcheck31 import g6
cnt = 0
for fn in sys.argv[1:]:
    for line in open(fn):
        f = line.split(); s = f[0]
        P = [int(t) for t in f[1].split('-')]
        c1, a1, c2, a2 = [int(t) for t in f[-1][2:].split(',')]
        n, E = g6(s)
        assert len({c1, a1, c2, a2}) == 4
        assert P[0] == c1 and P[-1] == c2 and a1 not in P and a2 not in P and len(set(P)) == len(P)
        deg = [0] * n
        for i, j in E: deg[i] += 1; deg[j] += 1
        assert all(d % 2 for d in deg)
        assert (min(c1, a1), max(c1, a1)) not in E and (min(c2, a2), max(c2, a2)) not in E
        used = set(); ends = [0] * n
        for p in [f[1]] + f[2:-1]:
            vs = [int(t) for t in p.split('-')]
            assert len(set(vs)) == len(vs) >= 2
            for a, b in zip(vs, vs[1:]):
                e = (min(a, b), max(a, b)); assert e in E and e not in used; used.add(e)
            ends[vs[0]] += 1; ends[vs[-1]] += 1
        assert used == E and ends == [1] * n
        cnt += 1
print('checked', cnt, 'joint decompositions: all valid')

"""Audit A22c: check the repo's random J files (as g6(J - z)): J = G' + z(evens) 3-connected, z the
only even vertex, d(z) = 6, other degrees 3/5; count pairings, parallel-pair pairings, simple ones."""
import sys
from count_J import g6_decode, three_connected, pairings
OUT = '/home/user/Manuscripts/manuscripts/terminal-matching/scripts/out'
for name in sys.argv[1:]:
    lines = [l.strip() for l in open(f'{OUT}/{name}') if l.strip()]
    bad = tot = par = simple = 0
    for s in lines:
        n, B = g6_decode(s)
        deg = [sum(r) for r in B]
        ev = [v for v in range(n) if deg[v] % 2 == 0]
        A = [row[:] + [1 if v in ev else 0] for v, row in enumerate(B)]
        A.append([1 if v in ev else 0 for v in range(n)] + [0])
        dJ = [sum(r) for r in A]
        okdeg = len(ev) == 6 and all(d in (3, 5) for d in dJ[:n]) and dJ[n] == 6
        if not okdeg or not three_connected(n + 1, A):
            bad += 1
        for p in pairings(ev):
            tot += 1
            if any(B[a][b] for a, b in p): par += 1
            else: simple += 1
    print(f'{name}: J {len(lines)} (bad {bad}), pairings {tot}, parallel {par}, simple {simple}')

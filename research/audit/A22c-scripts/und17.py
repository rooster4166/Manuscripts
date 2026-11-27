"""Audit A22c: the three order-17 queries that ptm.c left undecided at budget 2e6, decided exactly
by the independent oracle (G = (J - z) + F as a multigraph, all six end prescriptions)."""
import time
from dlib import solve, check_decomp, check_constraints
from count_J import g6_decode
for line in open('/home/user/Manuscripts/manuscripts/terminal-matching/scripts/out/d6_r17_und.txt'):
    t = line.split(); s = t[0]; v = list(map(int, t[1:]))
    F = [(v[0], v[1]), (v[2], v[3]), (v[4], v[5])]
    n, B = g6_decode(s)
    E = [(a, b) for b in range(n) for a in range(b) if B[a][b]]
    fid = []
    for f in F:
        fid.append(len(E)); E.append(f)
    for i, f in enumerate(fid):
        for x in F[i]:
            spec = {g: -1 for g in fid}; spec[f] = x
            t0 = time.time()
            D = solve(n, E, set(range(n)), spec=spec)
            ok = D is not None
            if ok:
                check_decomp(n, E, D, set(range(n))); check_constraints(D, spec=spec)
            print(s, F, 'end', x, 'PTM(e@x)', ok, f'{time.time()-t0:.1f}s', flush=True)

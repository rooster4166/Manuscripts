import itertools, sys
from k1x_helpers import *
cap = int(sys.argv[1]); part = int(sys.argv[2]); nparts = int(sys.argv[3])
reps = sorted({canon(S, xr) for k in range(6) for S in itertools.combinations(range(5), k) for xr in (0, 1)})
reps.sort(key=lambda t: (0 if (c in t[0]) != (d in t[0]) else 1, t))
for S, xr in reps[part::nparts]:
    E = CORES['K1'] + [(5, t) for t in (a, b, e)] + [(6, t) for t in S] + ([(5, 6)] if xr else [])
    r = certW(E, cap); kind = 'W'
    if r is None: r = certB(E, cap); kind = 'B'
    tag = ''.join(NAMES[t] for t in S) or '0'
    print('mask', tag, 'xr=%d' % xr, ('%s-cert |H|=%d' % (kind, len(r))) if r is not None else 'NONE(cap %d)' % cap,
          'distinguishes c,d' if (c in S) != (d in S) else '', flush=True)

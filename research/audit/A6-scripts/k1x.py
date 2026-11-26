"""K1 core, r = 5 with N_T(r) = abe, exterior x = 6 with N_T(x) = S and xr in {0,1}.
W-setting (leaf at r external): T even, r odd, x odd; one even local site after holding.
Report, per orbit representative under (a b), (c d), whether an unconditional
seven-site certificate exists (exhaustive over held sets)."""
import itertools, sys
from fancert import search
from sevensite import CORES, NAMES
from bank2 import runB, runW
a, b, c, d, e = range(5)
def canon(S, xr):
    best = None
    for pa in (False, True):
        for pc in (False, True):
            m = {a: b if pa else a, b: a if pa else b, c: d if pc else c, d: c if pc else d, e: e}
            key = (tuple(sorted(m[t] for t in S)), xr)
            best = key if best is None or key < best else best
    return best
reps = sorted({canon(S, xr) for k in range(6) for S in itertools.combinations(range(5), k) for xr in (0, 1)})
idx, step = int(sys.argv[1]), int(sys.argv[2])
for S, xr in reps[idx::step]:
    rW = runW('K1', (a, b, e), S, bool(xr))
    res = 'W-cert' if rW else None
    if not rW:
        rB = runB('K1', (a, b, e), S, bool(xr))
        res = 'B-cert' if rB else 'NONE'
    tag = ''.join(NAMES[t] for t in S) or '0'
    print('mask', tag, 'xr=%d' % xr, res, 'distinguishes c,d' if (c in S) != (d in S) else '', flush=True)

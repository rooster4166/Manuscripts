"""Second bank: B-setting.  Local T=0..4 (even), r=5 (even), x=6 (odd).
Seeds: hold H with 0 even local sites (all ends 1) or exactly 2 even sites p,q,
p doubled (needs a surviving local edge at p), q blank.  Goal: final b[r] >= 2.
Also a W-setting variant (leaf at r external): T even, r odd, x odd, one even site."""
import itertools, sys
from fancert import search
from sevensite import CORES, NAMES
def seeds_B(E, par, m):
    for s in sorted(range(1 << m), key=lambda s: bin(s).count('1')):
        H = [E[i] for i in range(m) if s >> i & 1]
        p = list(par)
        for x, y in H: p[x] ^= 1; p[y] ^= 1
        ev = [i for i, q in enumerate(p) if q == 0]
        if len(ev) == 0:
            yield H, tuple(1 for _ in p)
        elif len(ev) == 2:
            pres = set(map(frozenset, E)) - set(map(frozenset, H))
            for pp, qq in (ev, ev[::-1]):
                if any(pp in e for e in pres):
                    b0 = [1] * len(p); b0[pp] = 2; b0[qq] = 0
                    yield H, tuple(b0)
def runB(core, A, S, xr=True):
    E = CORES[core] + [(5, t) for t in A] + [(6, t) for t in S] + ([(5, 6)] if xr else [])
    par = [0, 0, 0, 0, 0, 0, 1]
    for H, b0 in seeds_B(E, par, len(E)):
        c = search(7, E, H, b0, goal=lambda b: b[5] >= 2)
        if c is not None: return H, b0, c
    return None
def runW(core, A, S, xr):
    """W-setting with leaf at r treated as external."""
    E = CORES[core] + [(5, t) for t in A] + [(6, t) for t in S] + ([(5, 6)] if xr else [])
    par = [0, 0, 0, 0, 0, 1, 1]
    m = len(E)
    for s in sorted(range(1 << m), key=lambda s: bin(s).count('1')):
        H = [E[i] for i in range(m) if s >> i & 1]
        p = list(par)
        for x, y in H: p[x] ^= 1; p[y] ^= 1
        if sum(1 for q in p if q == 0) != 1: continue
        b0 = tuple(1 if q else 0 for q in p)
        c = search(7, E, H, b0)
        if c is not None: return H, b0, c
    return None
def tag(S): return ''.join(NAMES[t] for t in S) or '0'
if __name__ == '__main__':
    which = sys.argv[1]
    T = range(5)
    allS = [S for k in range(6) for S in itertools.combinations(T, k)]
    if which == 'K2':
        for A in [(0, 1, 2, 3), (0, 1, 3, 4)]:
            unc = []
            for S in allS:
                rB = runB('K2', A, S, True)
                if rB is None:
                    rW = runW('K2', A, S, True)
                    if rW is None: unc.append(tag(S))
            print('K2 A=', tag(A), 'x-masks (xr present) without certificate:', unc, flush=True)
    elif which == 'K1x':
        A = (0, 1, 4)
        for xr in (False, True):
            unc = []
            for S in allS:
                rW = runW('K1', A, S, xr)
                if rW is None:
                    rB = runB('K1', A, S, xr)
                    if rB is None: unc.append(tag(S))
            print('K1 A=abe xr=', xr, 'masks without certificate:', unc, flush=True)

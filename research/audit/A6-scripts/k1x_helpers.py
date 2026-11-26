import itertools
from fancert import search
from sevensite import CORES, NAMES
a, b, c, d, e = range(5)
def canon(S, xr):
    best = None
    for pa in (False, True):
        for pc in (False, True):
            m = {a: b if pa else a, b: a if pa else b, c: d if pc else c, d: c if pc else d, e: e}
            key = (tuple(sorted(m[t] for t in S)), xr)
            best = key if best is None or key < best else best
    return best
def subsets_upto(m, cap):
    for k in range(cap + 1):
        for comb in itertools.combinations(range(m), k):
            yield comb
def certW(E, cap):
    par = [0, 0, 0, 0, 0, 1, 1]
    for comb in subsets_upto(len(E), cap):
        H = [E[i] for i in comb]
        p = list(par)
        for x, y in H: p[x] ^= 1; p[y] ^= 1
        if sum(1 for q in p if q == 0) != 1: continue
        if search(7, E, H, tuple(1 if q else 0 for q in p)) is not None: return H
    return None
def certB(E, cap):
    par = [0, 0, 0, 0, 0, 0, 1]
    for comb in subsets_upto(len(E), cap):
        H = [E[i] for i in comb]
        p = list(par)
        for x, y in H: p[x] ^= 1; p[y] ^= 1
        ev = [i for i, q in enumerate(p) if q == 0]
        seeds = []
        if not ev: seeds.append(tuple([1] * 7))
        elif len(ev) == 2:
            pres = set(map(frozenset, E)) - set(map(frozenset, H))
            for pp, qq in (ev, ev[::-1]):
                if any(pp in f for f in pres):
                    b0 = [1] * 7; b0[pp] = 2; b0[qq] = 0; seeds.append(tuple(b0))
        for b0 in seeds:
            if search(7, E, H, b0, goal=lambda bb: bb[5] >= 2) is not None: return H
    return None

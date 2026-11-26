"""Conditional certificates for the K1 mask cde: c is assumed to have a retained
external edge (to an exterior vertex of type acde/abcde, which keeps one end),
so the leaf trick may double c even if c keeps no local edge."""
import itertools
from k1x_helpers import *
from fancert import search
def certB_cond(E, cap, extra_pos):
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
                if pp in extra_pos or any(pp in f for f in pres):
                    b0 = [1] * 7; b0[pp] = 2; b0[qq] = 0; seeds.append(tuple(b0))
        for b0 in seeds:
            if search(7, E, H, b0, goal=lambda bb: bb[5] >= 2) is not None: return H, b0
    return None
for xr in (0, 1):
    E = CORES['K1'] + [(5, t) for t in (a, b, e)] + [(6, t) for t in (c, d, e)] + ([(5, 6)] if xr else [])
    r = certB_cond(E, 9, {c})
    print('cde xr=%d conditional (retained edge at c):' % xr, 'CERT held=%s seed=%s' % (r[0], r[1]) if r else 'NONE (cap 9)', flush=True)

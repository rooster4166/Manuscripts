import itertools, time
from seglib import *
tp = TwoPath()
h = 8
orders = cycle_orders(h)
print("cycle templates:", len(orders))
fail_small = 0; G = []; meta = []
for o in orders:
    segs = segments(h, o, 'cycle'); n = len(segs)
    for k in (0, 1):
        for S in itertools.combinations(range(n), k):
            S = frozenset(S)
            if is_simple(segs, S):
                G.append(graph(h, segs, S)); meta.append(('small', o, S))
    for S in minimal_sets(segs, 'cycle'):
        G.append(graph(h, segs, S)); meta.append(('min2', o, S))
res = tp.batch(G)
fs = sum(1 for i, ok in enumerate(res) if not ok and meta[i][0] == 'small')
fm = [meta[i] for i, ok in enumerate(res) if not ok and meta[i][0] == 'min2']
tot_small = sum(1 for m in meta if m[0] == 'small')
print("simple sets of size<=1:", tot_small, "failing:", fs, "; minimal sets of size>=2:", sum(1 for m in meta if m[0]=='min2'), "failing:", len(fm))

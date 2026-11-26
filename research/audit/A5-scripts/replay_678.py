import sys, itertools, time
from seglib import *
tp = TwoPath()
for h in (6, 7):
    for kind in ('path', 'cycle'):
        t = time.time()
        orders = path_orders(h) if kind == 'path' else cycle_orders(h)
        nsets = 0; fails = []
        G = []; meta = []
        for o in orders:
            segs = segments(h, o, kind)
            for S in minimal_sets(segs, kind):
                assert is_simple(segs, S)
                nsets += 1
                G.append(graph(h, segs, S)); meta.append((o, tuple(sorted(S))))
        res = tp.batch(G)
        fails = [meta[i] for i, ok in enumerate(res) if not ok]
        print(f"h={h} {kind}: orders={len(orders)} minimal sets={nsets} failing={len(fails)} {fails[:5]} ({time.time()-t:.1f}s)", flush=True)

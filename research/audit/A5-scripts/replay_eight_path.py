import itertools, time
from seglib import *
tp = TwoPath()
h = 8
t = time.time()
orders = path_orders(h)
print("path templates:", len(orders))
D = dihedral(h)
E = canon_path((0,3,4,7,6,1,2,5), D)
nopair = 0; failing_orders = {}; G = []; meta = []
for o in orders:
    segs = segments(h, o, 'path'); cls = classes(segs)
    if not cls:
        nopair += 1
        # all-direct: 15 edges on 8 vertices -> fails (2 paths <= 14 edges); confirm with checker
        G.append(graph(h, segs, frozenset())); meta.append((o, 'direct'))
        for i in range(len(segs)):
            G.append(graph(h, segs, frozenset([i]))); meta.append((o, (i,)))
    else:
        for ch in itertools.product(*cls):
            G.append(graph(h, segs, frozenset(ch))); meta.append((o, tuple(sorted(ch))))
res = tp.batch(G)
direct_fail = sum(1 for i, ok in enumerate(res) if meta[i][1] == 'direct' and not ok)
other_fail = [meta[i] for i, ok in enumerate(res) if meta[i][1] != 'direct' and not ok]
print("orders with simple unsubdivided core:", nopair, " of which fail:", direct_fail)
bad = sorted(set(o for o, S in other_fail))
print("orders failing with >=1 subdivision (minimal sets):", bad, "E canon:", E)
for o in bad:
    segs = segments(h, o, 'path'); cls = classes(segs)
    print(" order", o, "parallel classes", [[segs[i] for i in c] for c in cls])
    # all sets hitting each class (3^k) and everything else direct
    pairsets = []
    for choice in itertools.product(*[[ (c[0],), (c[1],), (c[0], c[1]) ] for c in cls]):
        pairsets.append(frozenset(itertools.chain(*choice)))
    r = tp.batch([graph(h, segs, S) for S in pairsets])
    print("  pair-only sets:", len(pairsets), "failing:", sum(1 for x in r if not x))
    others = [i for i in range(len(segs)) if all(i not in c for c in cls)]
    G2 = [graph(h, segs, S | {i}) for S in pairsets for i in others]
    r2 = tp.batch(G2)
    print("  + one non-pair segment:", len(G2), "failing:", sum(1 for x in r2 if not x))
print(f"({time.time()-t:.0f}s)")

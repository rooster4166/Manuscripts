"""h<=5 exhaustive (labelled orders, all subdivision sets): classify failures.
Also h=6,7 exhaustive over all simple subdivision sets (orbit reps)."""
import itertools, time, collections
from seglib import *
tp = TwoPath()

def all_orders(h, kind):
    if kind == 'path':
        return list(itertools.permutations(range(h)))
    return [(0,) + p for p in itertools.permutations(range(1, h))]

def simple_general(h, segs, S, kind):
    # any parallel class (size>=2) may have at most one direct segment;
    # for h==2 each cycle needs length>=3 -> its two segments not both direct (covered by class rule)
    cl = {}
    for i, (a, b) in enumerate(segs):
        cl.setdefault(frozenset((a, b)), []).append(i)
    for v in cl.values():
        if sum(1 for i in v if i not in S) > 1: return False
    return True

for h in range(2, 6):
    for kind in ('path', 'cycle'):
        if kind == 'cycle' and h < 3:
            # two cycles through exactly 2 common vertices: C=0-1 twice, D=0-1 twice
            segs = [(0, 1), (1, 0), (0, 1), (1, 0)]
            orders = [None]
        else:
            orders = all_orders(h, kind)
        G = []; meta = []
        for o in orders:
            if o is not None:
                segs = segments(h, o, kind)
            n = len(segs)
            for k in range(n + 1):
                for S in itertools.combinations(range(n), k):
                    S = frozenset(S)
                    if not simple_general(h, segs, S, kind): continue
                    G.append(graph(h, segs, S)); meta.append((o, tuple(sorted(S)), segs))
        res = tp.batch(G)
        fails = [meta[i] for i, ok in enumerate(res) if not ok]
        summary = collections.Counter(len(f[1]) for f in fails)
        print(f"h={h} {kind}: tested={len(G)} failing={len(fails)} by #subdivided={dict(summary)}")
        for o, S, segs in fails[:3]:
            print("   e.g.", o, S, [segs[i] for i in S])
        if kind == 'path' and fails:
            # check each failing one is K5-ab (+tails): all direct, h=5
            assert all(len(S) == 0 and h == 5 for o, S, segs in fails)
        if kind == 'cycle' and fails:
            assert all(len(S) <= 1 and h == 5 for o, S, segs in fails)

for h in (6, 7):
    for kind in ('path', 'cycle'):
        t = time.time()
        orders = path_orders(h) if kind == 'path' else cycle_orders(h)
        lb = 1 if kind == 'path' else 2
        tot = 0; nf = 0; ex = []
        for o in orders:
            segs = segments(h, o, kind); n = len(segs)
            G = []; meta = []
            for k in range(lb, n + 1):
                for S in itertools.combinations(range(n), k):
                    S = frozenset(S)
                    if not is_simple(segs, S): continue
                    G.append(graph(h, segs, S)); meta.append(S)
            res = tp.batch(G); tot += len(G)
            for i, ok in enumerate(res):
                if not ok: nf += 1; ex.append((o, sorted(meta[i])))
        print(f"h={h} {kind} ALL simple sets with >= {lb} subdivided: tested={tot} failing={nf} {ex[:3]} ({time.time()-t:.0f}s)", flush=True)

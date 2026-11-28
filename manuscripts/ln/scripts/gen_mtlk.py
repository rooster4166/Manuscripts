"""gen_mtlk.py K SMAX [flags] -- MTL(k) instances: <= 1 even vertex g; K leaf tails (c_i at w_i
avoiding A_i, |A_i| <= SMAX), c_i distinct, w_i not a tail leaf, A_i disjoint from {c_i, w_i},
every x in A_i non-adjacent to w_i (flag 'gadj': x ~ w_i allowed when x = g).
Writes lnsolve lines with S c_i x.  Random sampling of tail systems per graph (flag 'all' = all)."""
import sys, random, itertools
from lnlib import g6_decode
K = int(sys.argv[1]); SMAX = int(sys.argv[2]); flags = set(sys.argv[3:])
rng = random.Random(7)
PER = 200
for line in sys.stdin:
    gs = line.strip()
    if not gs: continue
    n, adj = g6_decode(gs)
    deg = [len(a) for a in adj]
    ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
    if len(ev) > 1: continue
    g = ev[0] if ev else None
    leaves = [v for v in range(n) if deg[v] == 1]
    if len(leaves) < K: continue
    def allowed(c, w):
        return [x for x in range(n) if x not in (c, w) and (x not in adj[w] or ('gadj' in flags and x == g)) and ('leafok' in flags or x not in leaves)]
    combos = list(itertools.combinations(leaves, K))
    out = set()
    for _ in range(PER):
        cs = rng.choice(combos)
        ws = [next(iter(adj[c])) for c in cs]
        if any(w in cs for w in ws): continue
        toks = [gs]
        ok = True
        for c, w in zip(cs, ws):
            al = allowed(c, w)
            s = rng.randint(1, SMAX)
            if len(al) < s: ok = False; break
            for x in rng.sample(al, s): toks += ['S', str(c), str(x)]
        if ok: out.add(' '.join(toks))
    for o in sorted(out): print(o)

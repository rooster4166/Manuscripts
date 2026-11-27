"""Case I failures: chain length at failure, and where u' sits."""
import random, sys
import msl
from collections import Counter

def run(trials, seed):
    rng = random.Random(seed)
    stats = Counter()
    for it in range(trials):
        n = rng.choice([9, 11, 13])
        K = msl.random_odd_graph(n - 1, rng.uniform(0.2, 0.4), rng)
        if K is None: continue
        xs = [x for x in K if len(K[x]) >= 3]
        if not xs: continue
        x = rng.choice(xs); u0 = rng.choice(sorted(K[x]))
        K[x].discard(u0); K[u0].discard(x)
        l = n - 1; K[l] = {u0}; K[u0].add(l)
        z = x
        pairs = [p for p in msl.far_pairs(K, rng) if l not in p]
        partner = {}
        for s, t in pairs: partner[s] = t; partner[t] = s
        for u in sorted(K[z]):
            if u not in partner: continue
            up = partner[u]
            K1 = msl.copy(K); K1[z].discard(u); K1[u].discard(z)
            Ds = msl.all_decomps(K1, msl.lovasz_profile(K1), limit=3000, pairs=pairs)
            for D in Ds:
                chs = msl.fan_chains(D, z, u, K1)
                assert len(chs) == 1
                ch = chs[0]
                k = len(ch[0])
                D2 = msl.fan_exec(D, ch, u)
                ok = msl.separates(D2, pairs)
                xk, ik, sk = ch[1]
                Qs = D[ik]
                pos = 'end' if up in (Qs[0], Qs[-1]) else 'int'
                stats[(k, ok, pos if not ok else '-')] += 1
    for key in sorted(stats): print(key, stats[key])
run(int(sys.argv[1]), int(sys.argv[2]))

"""Minimiser property on harder instances: report the distribution of min |V(Q_z)| and whether
minimisers avoid [u]; generate Case-I configurations from cubic graphs (Case II merge then delete
xw) where single-edge end-paths are rarer."""
import random, sys, subprocess
from collections import Counter
import msl
from g6 import g6_to_adj

def configs_cubic(n, rng, count):
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {n}", shell=True, capture_output=True, text=True).stdout.split()
    rng.shuffle(gs)
    for s in gs[:count]:
        K0 = g6_to_adj(s)
        P = msl.far_pairs(K0, rng, perfect_only=True)
        if P is None: continue
        cls = {}
        for a, b in P: cls[a] = {a, b}; cls[b] = cls[a]
        x = rng.choice(sorted(K0)); u = rng.choice(sorted(K0[x]))
        H = msl.copy(K0); H[x].discard(u); H[u].discard(x)
        l = n; H[l] = {u}; H[u].add(l)
        cx = cls[x] | {l}
        for v in cx: cls[v] = cx
        sep = sorted({(a, b) for v in cls for a in cls[v] for b in cls[v] if a < b})
        for w in sorted(H[x]):
            K1 = msl.copy(H); K1[x].discard(w); K1[w].discard(x)
            yield K1, x, w, sep, cls

def main(n, count, seed):
    rng = random.Random(seed)
    dist = Counter(); tot = good = 0; bad = []
    for K1, z, u, sep, cls in configs_cubic(n, rng, count):
        Ds = msl.all_decomps(K1, msl.lovasz_profile(K1), limit=200000, pairs=sep)
        if not Ds: print("NO separating D'"); continue
        def Qz(D):
            return next(Q for Q in D if Q[0] == z or Q[-1] == z)
        m = min(len(Qz(D)) for D in Ds)
        dist[m] += 1
        mins = [D for D in Ds if len(Qz(D)) == m]
        tot += 1
        if all(not (set(Qz(D)) & cls[u]) for D in mins): good += 1
        else: bad.append((z, u, K1, sep))
    print(f"n={n}: configs {tot}, all minimisers avoid [u]: {good}; min |V(Q_z)| distribution {dict(dist)}")
    for b in bad[:3]: print("  BAD", b)
if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))

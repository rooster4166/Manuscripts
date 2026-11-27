"""CSEP with minimum colourings of the square: classes = colour classes of an optimal (or small)
proper colouring of K^2.  Every path must be rainbow."""
import random, sys, subprocess
import msl, oracle
from g6 import g6_to_adj

def square(K):
    S = {v: set(K[v]) for v in K}
    for v in K:
        for w in K[v]:
            S[v] |= K[w]
        S[v].discard(v)
    return S

def colour(S, k, rng):
    V = sorted(S, key=lambda v: -len(S[v]))
    col = {}
    def bt(i):
        if i == len(V): return True
        v = V[i]
        used = {col[w] for w in S[v] if w in col}
        cs = [c for c in range(k) if c not in used]
        rng.shuffle(cs)
        for c in cs:
            col[v] = c
            if bt(i + 1): return True
            del col[v]
        return False
    return dict(col) if bt(0) else None

def min_colouring(K, rng):
    S = square(K)
    k = max(len(K[v]) for v in K) + 1   # closed neighbourhoods are cliques of K^2: a valid lower bound
    while True:
        c = colour(S, k, rng)
        if c: return k, c
        k += 1

def main(n, ngraphs, per, seed, budget, mode):
    rng = random.Random(seed)
    if mode == 'cubic':
        gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {n}", shell=True, capture_output=True, text=True).stdout.split()
        rng.shuffle(gs); Ks = [g6_to_adj(s) for s in gs[:ngraphs]]
    else:
        Ks = []
        while len(Ks) < ngraphs:
            K = msl.random_odd_graph(n, rng.uniform(0.15, 0.35), rng)
            if K and all(K[v] for v in K): Ks.append(K)
    tot = fail = unk = 0
    from collections import Counter
    kc = Counter()
    for K in Ks:
        for _ in range(per):
            k, c = min_colouring(K, rng)
            kc[k] += 1
            cls = {}
            for v, x in c.items(): cls.setdefault(x, []).append(v)
            pairs = [(a, b) for cl in cls.values() for i, a in enumerate(cl) for b in cl[i+1:]]
            res = oracle.query("SB", K, msl.lovasz_profile(K), sep=pairs, seed=rng.randrange(1000), budget=budget)
            tot += 1
            if res == 0:
                fail += 1
                if fail <= 5: print("FAIL k=%d" % k, {v: sorted(K[v]) for v in K}, sorted(cls.values()), flush=True)
            elif res == 2:
                unk += 1
                print("UNDECIDED k=%d" % k, {v: sorted(K[v]) for v in K}, pairs, flush=True)
    print(f"{mode} n={n}: total {tot} fail {fail} unknown {unk} colours {dict(kc)}")

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6])

"""Class separation: partition V into classes of size r whose members are pairwise at distance
>= 3; does some Lovasz decomposition meet every class at most once per path?"""
import random, sys, subprocess
import msl, oracle
from g6 import g6_to_adj

def far_classes(K, r, rng, tries=300):
    D = {v: msl.dist(K, v) for v in K}
    V = list(K)
    for _ in range(tries):
        rng.shuffle(V)
        used, cls, ok = set(), [], True
        for v in V:
            if v in used: continue
            c = [v]
            cand = [w for w in V if w not in used and w != v]
            rng.shuffle(cand)
            for w in cand:
                if len(c) == r: break
                if all(D[w].get(y, 99) >= 3 for y in c): c.append(w)
            used |= set(c); cls.append(c)
        if sum(len(c) >= min(r, 3) for c in cls) >= len(cls) // 2:
            return cls
    return None

def main(n, r, ngraphs, per, seed, budget):
    rng = random.Random(seed)
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {n}", shell=True, capture_output=True, text=True).stdout.split()
    rng.shuffle(gs)
    tot = fail = unk = 0
    for s in gs[:ngraphs]:
        K = g6_to_adj(s)
        for _ in range(per):
            cls = far_classes(K, r, rng)
            if cls is None: continue
            pairs = [(a, b) for c in cls for i, a in enumerate(c) for b in c[i+1:]]
            res = oracle.query("SB", K, msl.lovasz_profile(K), sep=pairs, seed=rng.randrange(1000), budget=budget)
            tot += 1
            if res == 0:
                fail += 1
                if fail <= 3: print("FAIL", s, cls, flush=True)
            elif res == 2: unk += 1
    print(f"n={n} r={r}: total {tot} fail {fail} unknown {unk}")

if __name__ == '__main__':
    main(*map(int, sys.argv[1:7]))

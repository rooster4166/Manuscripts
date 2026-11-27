"""Generalised conflict graphs: union of r perfect pairings at distance >= 3 on cubic graphs.
Does some Lovasz decomposition avoid every conflict pair?  (cubsep 'given' accepts only a
matching, so we use the general oracle with query S, which accepts arbitrary pair lists.)"""
import random, sys, subprocess
import msl, oracle
from g6 import g6_to_adj

def main(n, r, per, seed, budget):
    rng = random.Random(seed)
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {n}", shell=True, capture_output=True, text=True).stdout.split()
    rng.shuffle(gs)
    tot = fail = unk = 0
    for s in gs[:200]:
        K = g6_to_adj(s)
        for _ in range(per):
            pairs = set()
            for _ in range(r):
                P = msl.far_pairs(K, rng, perfect_only=True)
                if P is None: break
                pairs |= {tuple(sorted(p)) for p in P}
            if not pairs: continue
            res = oracle.query("SB", K, msl.lovasz_profile(K), sep=sorted(pairs), seed=rng.randrange(1000), budget=budget)
            tot += 1
            if res == 0:
                fail += 1
                if fail <= 3: print("FAIL", s, sorted(pairs))
            elif res == 2: unk += 1
    print(f"n={n} r={r}: total {tot} fail {fail} unknown {unk}")

main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))

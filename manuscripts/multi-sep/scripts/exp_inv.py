"""Existence of strengthened invariants (cubic graphs, perfect pairings at distance >= 3):
  I1': separation + every end-path Q_x avoids the partners of x's neighbours.
"""
import random, sys, subprocess
import msl, oracle
from g6 import g6_to_adj

def main(n, ngraphs, per, seed, budget):
    rng = random.Random(seed)
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {n}", shell=True, capture_output=True, text=True).stdout.split()
    rng.shuffle(gs)
    tot = fail = unk = 0
    for s in gs[:ngraphs]:
        K = g6_to_adj(s)
        for _ in range(per):
            P = msl.far_pairs(K, rng, perfect_only=True)
            if P is None: continue
            part = {}
            for a, b in P: part[a] = b; part[b] = a
            avoid = {x: {part[w] for w in K[x]} for x in K}
            res = oracle.query("ASB", K, msl.lovasz_profile(K), sep=P, avoid=avoid, seed=rng.randrange(1000), budget=budget)
            tot += 1
            if res == 0: fail += 1
            elif res == 2: unk += 1
    print(f"n={n}: total {tot} fail {fail} unknown {unk}")
if __name__ == '__main__':
    main(*map(int, sys.argv[1:6]))

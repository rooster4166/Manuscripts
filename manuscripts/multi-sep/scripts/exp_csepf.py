"""CSEP-F: cubic K, perfect pairing; each vertex v gets one forbidden class f(v) = [w] for a random
w with [w] disjoint from N[v] (frac = fraction of vertices constrained).  Is there a separating
Lovasz decomposition with Q_v avoiding f(v) for all constrained v?"""
import random, sys, subprocess
import msl, oracle
from g6 import g6_to_adj

def main(n, ngraphs, per, seed, budget, frac, mind):
    rng = random.Random(seed)
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {n}", shell=True, capture_output=True, text=True).stdout.split()
    rng.shuffle(gs)
    tot = fail = unk = 0
    for s in gs[:ngraphs]:
        K = g6_to_adj(s)
        D = {v: msl.dist(K, v) for v in K}
        for _ in range(per):
            P = msl.far_pairs(K, rng, perfect_only=True)
            if P is None: continue
            part = {}
            for a, b in P: part[a] = b; part[b] = a
            avoid = {}
            for v in K:
                if rng.random() > frac: continue
                cand = [w for w in K if D[v][w] >= mind and D[v][part[w]] >= 2]
                if cand:
                    w = rng.choice(cand); avoid[v] = {w, part[w]}
            res = oracle.query("ASB", K, msl.lovasz_profile(K), sep=P, avoid=avoid, seed=rng.randrange(1000), budget=budget)
            tot += 1
            if res == 0: fail += 1
            elif res == 2: unk += 1
    print(f"n={n} frac={frac} mind={mind}: total {tot} fail {fail} unknown {unk}")
main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), float(sys.argv[6]), int(sys.argv[7]))

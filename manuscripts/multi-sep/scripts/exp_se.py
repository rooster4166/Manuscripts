"""(SE): can the end-path of a prescribed odd vertex z be a single edge (some neighbour v), in a
separating/rainbow Lovasz decomposition?  Also (SEv): for a prescribed edge zv.
Query: avoid[z] = V - N[z] forces Q_z inside N[z] (L-infinity); single edge is stronger."""
import random, sys, subprocess
import msl, oracle
from g6 import g6_to_adj
from exp_ee import one_even

def main(trials, seed, budget, kind):
    rng = random.Random(seed)
    tot = fail = unk = 0
    for it in range(trials):
        n = rng.choice([8, 10, 12, 14])
        if kind == 'oneeven':
            r = one_even(n, rng.uniform(0.15, 0.45), rng)
            if r is None: continue
            K, _ = r
        else:
            K = msl.random_odd_graph(n, rng.uniform(0.15, 0.45), rng)
            if not K or any(not K[v] for v in K): continue
        P = msl.far_pairs(K, rng)
        for z in rng.sample(sorted(K), min(3, len(K))):
            if len(K[z]) % 2 == 0: continue
            # L-infinity: Q_z inside N[z]
            avoid = {z: set(K) - K[z] - {z}}
            res = oracle.query("ASB", K, msl.lovasz_profile(K), sep=P, avoid=avoid, seed=rng.randrange(1000), budget=budget)
            tot += 1
            if res == 0:
                fail += 1
                if fail <= 3: print("LINF-FAIL", z, {v: sorted(K[v]) for v in K}, P, flush=True)
            elif res == 2: unk += 1
    print(f"{kind}: L-inf with separation: total {tot} fail {fail} unknown {unk}")
if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])

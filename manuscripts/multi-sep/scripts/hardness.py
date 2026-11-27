"""Hardness of MSEP instances: fraction of random Lovasz decompositions (random Lovasz induction)
that separate all pairs.  Search for the hardest instances among random all-odd graphs and cubic
graphs; run the exact oracle on the hardest."""
import random, sys
import msl, randlov, oracle
from strat_rreg import random_regular

def frac(K, P, rng, samples=60):
    good = 0
    for _ in range(samples):
        D = randlov.lovasz_random(K, rng)
        good += msl.separates(D, P)
    return good / samples

def main(count, seed, mode):
    rng = random.Random(seed)
    res = []
    for it in range(count):
        if mode == 'cubic':
            n = rng.choice([12, 14, 16, 18, 20])
            K = random_regular(n, 3, rng)
        elif mode == 'reg5':
            n = rng.choice([24, 28, 32])
            K = random_regular(n, 5, rng)
        else:
            n = rng.choice([12, 14, 16, 18])
            K = msl.random_odd_graph(n, rng.uniform(0.15, 0.4), rng)
            if K is None or any(not K[v] for v in K): continue
        if K is None: continue
        P = msl.far_pairs(K, rng, perfect_only=(mode != 'rand'), tries=300)
        if not P: continue
        f = frac(K, P, rng)
        res.append((f, K, P))
    res.sort(key=lambda t: t[0])
    print(mode, "fractions: min %.3f median %.3f" % (res[0][0], res[len(res)//2][0]))
    for f, K, P in res[:8]:
        r = oracle.query("SB", K, msl.lovasz_profile(K), sep=P, seed=1, budget=20000000)
        if r != 1:
            D = randlov.find_separating(K, P, rng, tries=300)
            r = 1 if D else r
        print("  hardest: frac %.3f n=%d m=%d oracle/cert=%s" % (f, len(K), len(msl.edges(K)), r), flush=True)
        if r == 0: print("COUNTEREXAMPLE", {v: sorted(K[v]) for v in K}, P)
if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3])

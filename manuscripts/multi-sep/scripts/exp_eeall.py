"""(EE-all): K with one even vertex z.  Does K - z have a separating decomposition with b = 0 on
N(z) and b = 1 elsewhere (then the paths u_i z u_j complete it)?  Also ELOV2: graphs with exactly
two even vertices at distance 2 or >= 3, no classes."""
import random, sys
import msl, oracle
from exp_ee import one_even
from exp_min2 import configs_cubic

def main(trials, seed, budget, kind):
    rng = random.Random(seed)
    tot = fail = unk = 0
    gen = []
    if kind == 'rand':
        for it in range(trials):
            n = rng.choice([8, 10, 12, 14])
            r = one_even(n, rng.uniform(0.15, 0.45), rng)
            if r is None: continue
            K, z = r
            gen.append((K, z, msl.far_pairs(K, rng)))
    else:
        for K1, x, w, sep, cls in configs_cubic(int(kind), rng, trials):
            gen.append((K1, w, sep))
    for K, z, sep in gen:
        K2 = msl.copy(K)
        for v in K2[z]: K2[v].discard(z)
        K2[z] = set()
        b = {v: (len(K2[v]) % 2) for v in K2}
        sep2 = [(a, c) for a, c in sep if z not in (a, c)]
        r = oracle.query("SB", K2, b, sep=sep2, seed=rng.randrange(1000), budget=budget)
        tot += 1
        if r == 0: fail += 1
        elif r == 2: unk += 1
    print(f"{kind}: EE-all total {tot} fail {fail} unknown {unk}")
if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])

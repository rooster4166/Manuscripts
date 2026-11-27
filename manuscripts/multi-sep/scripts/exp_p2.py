"""(P2): K with exactly one even vertex z: is there a rainbow (separating) Lovasz decomposition in
which some path is v z u (length two, centred at z)?  Equivalently, for some u in N(z), a
separating decomposition of K - uz whose path at z is a single edge."""
import random, sys
import msl, oracle
from exp_ee import one_even
from exp_min2 import configs_cubic

def p2(K, z, sep, rng, budget):
    """exists u: K - uz has separating D' with Q_z single edge: avoid[z] = all but N[z] and the
    single-edge requirement ~ Q_z inside N[z] and length one: we test Q_z inside N[z] - (nbrs adjacent to other nbrs)?
    Simplest exact test: for each u, each v in N(z)-u: K - uz - zv with z,v,u even, b=0 there: P query."""
    for u in sorted(K[z]):
        for v in sorted(K[z]):
            if v == u: continue
            K2 = msl.copy(K); K2[z] -= {u, v}; K2[u].discard(z); K2[v].discard(z)
            b = msl.lovasz_profile(K2)
            # in K2 the path {z,v} is removed: z has deg d-2 (even), u even, v even, b=0 there
            # separation: pairs as given; the removed 2-path v z u is rainbow automatically
            r = oracle.query("SB", K2, b, sep=sep, seed=rng.randrange(1000), budget=budget)
            if r == 1: return 1
            if r == 2: return 2
    return 0

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
            # K1 has even w; z := w
            gen.append((K1, w, sep))
    for K, z, sep in gen:
        r = p2(K, z, sep, rng, budget)
        tot += 1
        if r == 0:
            fail += 1
            if fail <= 3: print("P2-FAIL", z, {v: sorted(K[v]) for v in K}, sep, flush=True)
        elif r == 2: unk += 1
    print(f"{kind}: P2 total {tot} fail {fail} unknown {unk}")
if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])

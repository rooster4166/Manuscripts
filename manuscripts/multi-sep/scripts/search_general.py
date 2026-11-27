"""Counterexample search for MSEP / CSEP on random all-odd graphs.
mode 'pair': perfect (or maximal) pairings at distance >= 3; mode 'col': classes = colour classes of
a minimum proper colouring of the square (strongest form, CSEP).  Budgeted oracle; undecided
instances are retried with larger budgets and reported."""
import random, sys, time
import msl, oracle
from exp_sqcol import min_colouring

def instance(rng, n):
    for _ in range(100):
        p = rng.choice([rng.uniform(0.12, 0.25), rng.uniform(0.25, 0.5)])
        K = msl.random_odd_graph(n, p, rng)
        if K and all(K[v] for v in K) and sum(len(K[v]) for v in K) // 2 <= 120:
            return K
    return None

def main(trials, seed, mode, nmin, nmax, budget):
    rng = random.Random(seed)
    stats = {}
    t0 = time.time()
    for it in range(trials):
        n = rng.choice(range(nmin, nmax + 1, 2))
        K = instance(rng, n)
        if K is None: continue
        if mode == 'pair':
            P = msl.far_pairs(K, rng)
            if not P: continue
            sep = P; tag = (n, 2 * len(P) == n)
        else:
            k, c = min_colouring(K, rng)
            cls = {}
            for v, x in c.items(): cls.setdefault(x, []).append(v)
            sep = [(a, b) for cl in cls.values() for i, a in enumerate(cl) for b in cl[i+1:]]
            tag = (n, k)
        res = 2; b = budget
        for att in range(4):
            res = oracle.query("SB", K, msl.lovasz_profile(K), sep=sep, seed=rng.randrange(10**6), budget=b)
            if res != 2: break
            b *= 4
        st = stats.setdefault(tag, [0, 0, 0]); st[0] += 1
        if res == 0:
            st[1] += 1
            print("FAIL", mode, {v: sorted(K[v]) for v in K}, sep, flush=True)
        elif res == 2:
            st[2] += 1
            print("UNDECIDED", mode, {v: sorted(K[v]) for v in K}, sep, flush=True)
    print("summary", mode, "(key) -> [total, fail, undecided]:", dict(sorted(stats.items())), "time", int(time.time() - t0))

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]))

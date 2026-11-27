"""CL / (EE) on larger cubic-derived Case I configurations, using random cubic graphs (configuration
model) instead of geng.  Same construction as exp_cl.py."""
import random, sys
import msl, oracle
from strat_rreg import random_regular

def main(n, count, seed, budget):
    rng = random.Random(seed)
    tot = fail = unk = 0
    for _ in range(count):
        K0 = random_regular(n, 3, rng)
        if K0 is None: continue
        P = msl.far_pairs(K0, rng, perfect_only=True)
        if P is None: continue
        cls = {}
        for a, b in P: cls[a] = {a, b}; cls[b] = cls[a]
        x = rng.choice(sorted(K0)); u = rng.choice(sorted(K0[x]))
        H = msl.copy(K0); H[x].discard(u); H[u].discard(x)
        l = n; H[l] = {u}; H[u].add(l)
        cx = cls[x] | {l}
        for v in cx: cls[v] = cx
        sep = sorted({(a, b) for v in cls for a in cls[v] for b in cls[v] if a < b})
        for w in sorted(H[x]):
            K1 = msl.copy(H); K1[x].discard(w); K1[w].discard(x)
            r = oracle.query("ASB", K1, msl.lovasz_profile(K1), sep=sep, avoid={x: cls[w]}, seed=rng.randrange(1000), budget=budget)
            tot += 1
            if r == 0:
                fail += 1; print("CL-FAIL", {v: sorted(K1[v]) for v in K1}, sep, x, w, flush=True)
            elif r == 2: unk += 1
    print(f"n={n}: (instance, w) total {tot} fail {fail} unknown {unk}")
if __name__ == "__main__":
    main(*map(int, sys.argv[1:5]))

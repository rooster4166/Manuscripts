"""(EE): K with exactly one even vertex z; for each neighbour u of z, is there a Lovasz
decomposition (rainbow w.r.t. classes, or no classes) with e(u) = uz, i.e. a decomposition of
K - uz in which Q_z avoids [u]?  Random graphs with one even vertex."""
import random, sys
import msl, oracle

def one_even(n, p, rng):
    for _ in range(200):
        K = msl.random_odd_graph(n, p, rng)
        if not K or any(not K[v] for v in K): continue
        xs = [x for x in K if len(K[x]) >= 3]
        if not xs: continue
        x = rng.choice(xs); u = rng.choice(sorted(K[x]))
        K[x].discard(u); K[u].discard(x)
        l = n; K[l] = {u}; K[u].add(l)
        return K, x
    return None

def main(trials, seed, budget, classes):
    rng = random.Random(seed)
    tot = fail = unk = 0
    for it in range(trials):
        n = rng.choice([8, 10, 12, 14])
        r = one_even(n, rng.uniform(0.15, 0.45), rng)
        if r is None: continue
        K, z = r
        sep = []
        cls = {v: {v} for v in K}
        if classes:
            P = msl.far_pairs(K, rng)
            sep = P
            for a, b in P: cls[a] = {a, b}; cls[b] = {a, b}
        for u in sorted(K[z]):
            K1 = msl.copy(K); K1[z].discard(u); K1[u].discard(z)
            res = oracle.query("ASB", K1, msl.lovasz_profile(K1), sep=sep, avoid={z: cls[u]}, seed=rng.randrange(1000), budget=budget)
            tot += 1
            if res == 0:
                fail += 1
                if fail <= 3: print("EE-FAIL", z, u, {v: sorted(K[v]) for v in K}, sep, flush=True)
            elif res == 2: unk += 1
    print(f"classes={classes}: (z,u) total {tot} fail {fail} unknown {unk}")
if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))

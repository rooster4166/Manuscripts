"""Two prescribed end edges: all-odd K, x, y far apart (distance >= 3), edges xu, yv.  Is there a
Lovasz decomposition with e(x) = xu and e(y) = yv?  Split graph: K - xu - yv + u lx + v ly, profile
b(x) = b(y) = 0, b(lx) = b(ly) = 1, separation pairs {x, lx}, {y, ly}."""
import random, sys
import msl, oracle

def main(trials, seed, budget, kmax):
    rng = random.Random(seed)
    tot = fail = unk = 0
    for it in range(trials):
        n = rng.choice([8, 10, 12, 14])
        K = msl.random_odd_graph(n, rng.uniform(0.15, 0.45), rng)
        if not K or any(not K[v] for v in K): continue
        k = rng.randint(2, kmax)
        D = {v: msl.dist(K, v) for v in K}
        V = list(K); rng.shuffle(V)
        S = []
        for v in V:
            if len(S) < k and all(D[v].get(s, 99) >= 3 for s in S): S.append(v)
        if len(S) < 2: continue
        H = msl.copy(K); b = msl.lovasz_profile(K); sep = []
        m = n
        for x in S:
            u = rng.choice(sorted(K[x]))
            H[x].discard(u); H[u].discard(x)
            H[m] = {u}; H[u].add(m)
            b[x] = 0; b[m] = 1; sep.append((x, m)); m += 1
        r = oracle.query("SB", H, b, sep=sep, seed=rng.randrange(1000), budget=budget)
        tot += 1
        if r == 0:
            fail += 1
            if fail <= 3: print("FAIL", S, {v: sorted(K[v]) for v in K}, flush=True)
        elif r == 2: unk += 1
    print(f"prescribed end edges at k<= {kmax} packed vertices: total {tot} fail {fail} unknown {unk}")
if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))

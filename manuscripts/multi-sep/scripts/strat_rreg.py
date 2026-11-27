"""Strategies on random d-regular graphs (configuration model) with perfect pairings at distance >= 3."""
import random, sys
import msl, coarsen, rotate

def random_regular(n, d, rng, tries=5000):
    for _ in range(tries):
        pts = [v for v in range(n) for _ in range(d)]
        rng.shuffle(pts)
        K = {v: set() for v in range(n)}
        ok = True
        for i in range(0, len(pts), 2):
            a, c = pts[i], pts[i + 1]
            if a == c or c in K[a]: ok = False; break
            K[a].add(c); K[c].add(a)
        if ok: return K
    return None

def main(n, d, count, which, seed):
    rng = random.Random(seed)
    ok = tot = 0
    for _ in range(count):
        K = random_regular(n, d, rng)
        if K is None: continue
        P = msl.far_pairs(K, rng, perfect_only=True, tries=500)
        if P is None: continue
        tot += 1
        if which == 'coarsen':
            D = coarsen.run(K, P, rng, budget=20000, tries=3)
        else:
            b = [5000]
            D = rotate.solve(msl.copy(K), [frozenset(p) for p in P], {}, 6, b)
        if D is not None:
            assert msl.is_decomp(K, D, msl.lovasz_profile(K)) and msl.separates(D, P)
            ok += 1
        print(f"  inst {tot}: {'ok' if D else 'FAIL'}", flush=True)
    print(f"n={n} d={d} {which}: {ok}/{tot}")

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], int(sys.argv[5]))

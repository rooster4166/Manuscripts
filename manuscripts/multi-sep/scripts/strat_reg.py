"""Coarsening (Case I/II) and rotation strategies on d-regular graphs (d odd) with perfect
pairings at distance >= mind; graphs from nauty geng (connected, d-regular)."""
import random, sys, subprocess
import msl, coarsen, rotate
from g6 import g6_to_adj

def main(n, d, count, mind, which, flags=""):
    rng = random.Random(3)
    out = subprocess.run(f"nauty-geng -cq -d{d} -D{d} {flags} {n}", shell=True, capture_output=True, text=True, timeout=600).stdout.split()
    rng.shuffle(out)
    ok = tot = 0
    for s in out[:count]:
        K = g6_to_adj(s)
        P = msl.far_pairs(K, rng, mind=mind, perfect_only=True)
        if P is None: continue
        tot += 1
        if which == 'coarsen':
            D = coarsen.run(K, P, rng, budget=20000, tries=5)
        else:
            b = [20000]
            D = rotate.solve(msl.copy(K), [frozenset(p) for p in P], {}, 8, b)
        if D is not None:
            assert msl.is_decomp(K, D, msl.lovasz_profile(K)) and msl.separates(D, P)
            ok += 1
    print(f"n={n} d={d} mind={mind} {which}: {ok}/{tot}")

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], sys.argv[6] if len(sys.argv) > 6 else "")

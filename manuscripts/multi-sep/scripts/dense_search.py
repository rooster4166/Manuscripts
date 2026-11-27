"""Randomised certification of MSEP on larger dense instances (random d-regular graphs with perfect
pairings at distance >= 3; optional class mode = min square colouring is too slow here)."""
import random, sys, time
import msl, randlov
from strat_rreg import random_regular

def main(n, d, count, seed, tries):
    rng = random.Random(seed)
    ok = tot = 0; t0 = time.time()
    for _ in range(count):
        K = random_regular(n, d, rng)
        if K is None: continue
        P = msl.far_pairs(K, rng, perfect_only=True, tries=500)
        if P is None: continue
        tot += 1
        D = randlov.find_separating(K, P, rng, tries=tries)
        ok += D is not None
        if D is None: print("NOT CERTIFIED", {v: sorted(K[v]) for v in K}, P, flush=True)
    print(f"n={n} d={d}: certified {ok}/{tot}  ({int(time.time()-t0)} s)")
if __name__ == "__main__":
    main(*map(int, sys.argv[1:6]))

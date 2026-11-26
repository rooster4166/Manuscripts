"""Random sanity checks of the two-vertex extension lemma (TVL) and of the
equivalence  TVL  <=>  Stage-Z flow feasible  <=>  (UH-Z) and (LH-Z)."""
import random, sys, itertools
from lf import pvec, check_decomp, hall_check_Z
from solvers import one_vertex_step, tvl_cpsat, stageZ_flow

def random_level(n, m, rng):
    col = {}
    for mm in range(1, m):
        new = one_vertex_step(mm, n, col, rng)
        assert new is not None, "Hilton step failed?!"
        col = new
    assert check_decomp(m, n, col)
    return col

def main(seed=0, trials=200, nmax=8):
    rng = random.Random(seed)
    stats = dict(inst=0, feas=0, infeas=0, mismatch=0)
    for tr in range(trials):
        n = rng.randint(3, nmax)
        # K = 2n+1-m >= 4 with room for U: need K >= 4
        K = rng.randint(4, 2 * n)
        m = 2 * n + 1 - K
        if m < 2: continue
        col = random_level(n, m, rng)
        p = pvec(m, n, col)
        cand = [i for i in range(n) if p[i] <= K - 1]
        umax = (K - 2) // 2
        if not cand or umax < 1: continue
        cand.sort(key=lambda i: (-p[i], rng.random()))
        U = set(cand[:rng.randint(1, min(umax, len(cand)))])
        for c in U:
            stats["inst"] += 1
            r1 = tvl_cpsat(m, n, col, U, c) is not None
            r2 = stageZ_flow(m, n, col, U, c)
            uh, lh, _ = hall_check_Z(m, n, col, U, c) if m <= 14 else (r2, r2, None)
            r3 = uh and lh
            if not (r1 == r2 == r3):
                stats["mismatch"] += 1
                print("MISMATCH", n, m, K, U, c, r1, r2, r3, p)
            if r1: stats["feas"] += 1
            else:
                stats["infeas"] += 1
                print("INFEASIBLE", n, m, K, sorted(U), c, p)
    print(stats)

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 0, int(sys.argv[2]) if len(sys.argv) > 2 else 100)

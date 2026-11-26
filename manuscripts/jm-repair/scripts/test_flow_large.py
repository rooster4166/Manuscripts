"""Theorem B on larger instances (n <= 14), flow test only (the brute-force cut check is
exponential in m).  Instances grown with the tight-biased Hilton steps of test_adversarial."""
import random, sys
from lf import pvec
from solvers import stageZ_flow
from test_adversarial import tight_step
rng = random.Random(int(sys.argv[1])); tot = ok = 0
for _ in range(int(sys.argv[2])):
    n = rng.randint(8, 14); K = rng.randint(4, 2 * n - 2); m = 2 * n + 1 - K
    col = {}
    for mm in range(1, m): col = tight_step(mm, n, col, rng)
    p = pvec(m, n, col); umax = (K - 2) // 2
    cand = [i for i in range(n) if p[i] == K - 1] or [i for i in range(n) if p[i] <= K - 1]
    if not cand or umax < 1: continue
    rng.shuffle(cand); U = set(cand[:umax])
    for c in U:
        tot += 1; r = stageZ_flow(m, n, col, U, c); ok += r
        if not r: print("INFEASIBLE", n, m, K, sorted(U), c, p)
print("instances", tot, "feasible", ok)

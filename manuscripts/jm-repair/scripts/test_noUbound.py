import random, sys
from lf import pvec, hall_check_Z
from solvers import tvl_cpsat, stageZ_flow
from test_random import random_level
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
fails = 0; inst = 0
for tr in range(int(sys.argv[2]) if len(sys.argv) > 2 else 60):
    n = rng.randint(3, 7); K = rng.randint(4, 2 * n); m = 2 * n + 1 - K
    if m < 2: continue
    col = random_level(n, m, rng); p = pvec(m, n, col)
    cand = [i for i in range(n) if p[i] <= K - 1]
    if len(cand) < 2: continue
    cand.sort(key=lambda i: -p[i])
    U = set(cand)              # as large as possible, ignoring 2|U| <= K-2
    if 2 * len(U) <= K - 2: continue
    for c in U:
        inst += 1
        r = tvl_cpsat(m, n, col, U, c) is not None
        assert r == stageZ_flow(m, n, col, U, c)
        if not r:
            fails += 1
            print("fail n=%d m=%d K=%d |U|=%d c=%d p=%s" % (n, m, K, len(U), c, p), hall_check_Z(m, n, col, U, c, want_witness=True))
print("instances", inst, "failures", fails)

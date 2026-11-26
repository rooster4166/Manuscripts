"""Adversarial variant of the TVL test: instances are grown by Hilton one-vertex steps
whose random objective keeps a random half of the colours as tight as possible
(few attachments), so that many colours sit at p_i = k or p_i = k-1.  U is then chosen
among the colours with p_i = k-1, as large as the hypothesis 2|U| <= k-2 allows,
and every c in U is tested."""
import random, sys
from ortools.sat.python import cp_model
from lf import components, edges_by_colour, pvec, hall_check_Z, check_decomp
from solvers import tvl_cpsat, stageZ_flow

def tight_step(m, n, col, rng):
    K = 2 * n + 1 - m; p = pvec(m, n, col); E = edges_by_colour(m, n, col)
    deg = [[0] * m for _ in range(n)]
    for i in range(n):
        for u, v in E[i]: deg[i][u] += 1; deg[i][v] += 1
    mdl = cp_model.CpModel(); b = {}
    for v in range(m):
        for i in range(n):
            if deg[i][v] <= 1: b[v, i] = mdl.NewBoolVar("")
        mdl.Add(sum(b[v, i] for i in range(n) if (v, i) in b) == 1)
    hot = set(rng.sample(range(n), (n + 1) // 2))
    obj = []
    for i in range(n):
        s = sum(b[v, i] for v in range(m) if (v, i) in b)
        mdl.Add(s <= 2); mdl.Add(p[i] + 1 - s <= K - 1)
        for (u, w) in components(m, E[i]):
            if u != w: mdl.Add(b[u, i] + b[w, i] <= 1)
        for v in range(m):
            if (v, i) in b: obj.append((-50 if i in hot else rng.randint(0, 20)) * b[v, i])
    mdl.Maximize(sum(obj))
    sol = cp_model.CpSolver(); sol.parameters.max_time_in_seconds = 10
    sol.parameters.random_seed = rng.randint(0, 10**6)
    st = sol.Solve(mdl); assert st in (cp_model.OPTIMAL, cp_model.FEASIBLE)
    new = dict(col)
    for (v, i), x in b.items():
        if sol.Value(x): new[(v, m)] = i
    return new

def main(seed, trials, nmax):
    rng = random.Random(seed); st = dict(inst=0, feas=0, mism=0, tightT=0, tightU=0)
    for _ in range(trials):
        n = rng.randint(4, nmax); K = rng.randint(4, 2 * n - 2); m = 2 * n + 1 - K
        col = {}
        for mm in range(1, m): col = tight_step(mm, n, col, rng)
        assert check_decomp(m, n, col)
        p = pvec(m, n, col)
        cand = [i for i in range(n) if p[i] == K - 1] or [i for i in range(n) if p[i] <= K - 1]
        umax = (K - 2) // 2
        if not cand or umax < 1: continue
        rng.shuffle(cand); U = set(cand[:umax])
        st["tightT"] += sum(1 for i in range(n) if i not in U and p[i] == K)
        st["tightU"] += sum(1 for i in U if p[i] == K - 1)
        for c in U:
            st["inst"] += 1
            r1 = tvl_cpsat(m, n, col, U, c) is not None
            r2 = stageZ_flow(m, n, col, U, c)
            r3 = all(hall_check_Z(m, n, col, U, c)[:2]) if m <= 15 else r2
            if not (r1 == r2 == r3): st["mism"] += 1; print("MISMATCH", n, m, U, c)
            if r1: st["feas"] += 1
            else: print("INFEASIBLE", n, m, K, sorted(U), c, p)
    print(st)
if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))

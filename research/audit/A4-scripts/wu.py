import sys, itertools, time
from common import *

def ham_cycles(n):
    eid = {frozenset(e): i for i, e in enumerate(itertools.combinations(range(n), 2))}
    out = []
    for perm in itertools.permutations(range(1, n)):
        if perm[0] > perm[-1]: continue
        cyc = (0,) + perm
        mask = 0
        for i in range(n):
            mask |= 1 << eid[frozenset((cyc[i], cyc[(i + 1) % n]))]
        out.append((cyc, mask))
    return eid, out

def rainbow(n, X, eid, cycles, time_limit=300, marks=None):
    """marks: list of edge-sets (colour classes) that must each lie in a distinct cycle, one class per cycle.
    Default: singletons of X."""
    k = (n - 1) // 2
    if marks is None:
        marks = [[e] for e in X]
    assert len(marks) == k
    markbits = [sum(1 << eid[frozenset(e)] for e in cl) for cl in marks]
    allmark = 0
    for b in markbits: allmark |= b
    model = cp_model.CpModel()
    cand = []  # (cycle index, colour)
    for ci, (cyc, mask) in enumerate(cycles):
        inter = mask & allmark
        for c, b in enumerate(markbits):
            if inter == b:
                cand.append((ci, c))
    x = [model.NewBoolVar("") for _ in cand]
    m = len(eid)
    by_edge = [[] for _ in range(m)]
    by_col = [[] for _ in range(k)]
    for j, (ci, c) in enumerate(cand):
        mk = cycles[ci][1]
        while mk:
            low = mk & -mk
            by_edge[low.bit_length() - 1].append(j)
            mk ^= low
        by_col[c].append(j)
    for e in range(m):
        model.AddExactlyOne(x[j] for j in by_edge[e])
    for c in range(k):
        model.AddExactlyOne(x[j] for j in by_col[c])
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = 4
    st = solver.Solve(model)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = [(cand[j][1], cycles[cand[j][0]][0]) for j in range(len(cand)) if solver.Value(x[j])]
        return solver.StatusName(st), sol
    return solver.StatusName(st), None

def check_decomp(n, sol, marks):
    seen = set()
    for c, cyc in sol:
        es = {frozenset((cyc[i], cyc[(i + 1) % n])) for i in range(n)}
        assert len(set(cyc)) == n
        assert not (es & seen)
        seen |= es
        allm = {frozenset(e) for cl in marks for e in cl}
        assert es & allm == {frozenset(e) for e in marks[c]}
    assert len(seen) == n * (n - 1) // 2
    return True

if __name__ == "__main__":
    for n in [int(a) for a in sys.argv[1:]]:
        k = (n - 1) // 2
        t0 = time.time()
        eid, cyc = ham_cycles(n)
        Xs = iso_classes_edge_sets(n, k)
        ok = 0
        for H in Xs:
            X = list(H.edges())
            st, sol = rainbow(n, X, eid, cyc)
            good = sol is not None and check_decomp(n, sol, [[e] for e in X])
            ok += good
            if not good: print("FAIL", n, X, st, flush=True)
        print(f"n={n}: Wu/JM rainbow decomposition found for {ok}/{len(Xs)} isomorphism classes of k-edge X; {len(cyc)} Ham cycles; {time.time()-t0:.1f}s", flush=True)

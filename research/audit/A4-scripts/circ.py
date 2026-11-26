"""Hamilton decompositions of K_n (n odd) with prescribed colour classes via CP-SAT AddCircuit."""
import itertools, sys
from ortools.sat.python import cp_model

def ham_decomp(n, classes, time_limit=600, workers=4, seed=0, forbid_extra=True):
    """classes: list of k lists of edges; class c must lie in cycle c; (if forbid_extra) no other class edge in cycle c
    (automatic since each edge has one colour).  Returns list of k cycles (vertex sequences) or None."""
    k = (n - 1) // 2
    assert len(classes) == k
    model = cp_model.CpModel()
    arc = {}
    for c in range(k):
        arcs = []
        for u in range(n):
            for v in range(n):
                if u != v:
                    b = model.NewBoolVar("")
                    arc[c, u, v] = b
                    arcs.append((u, v, b))
        model.AddCircuit(arcs)
    col = {}
    for u, v in itertools.combinations(range(n), 2):
        for c in range(k):
            y = model.NewBoolVar("")
            model.Add(arc[c, u, v] + arc[c, v, u] == y)
            col[c, u, v] = y
        model.AddExactlyOne(col[c, u, v] for c in range(k))
    for c, cl in enumerate(classes):
        for (u, v) in cl:
            u, v = min(u, v), max(u, v)
            model.Add(col[c, u, v] == 1)
    # symmetry: orientation of cycle c: fix nothing (fine)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = workers
    solver.parameters.random_seed = seed
    st = solver.Solve(model)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return solver.StatusName(st), None
    cycles = []
    for c in range(k):
        succ = {u: v for u in range(n) for v in range(n) if u != v and solver.Value(arc[c, u, v])}
        cyc = [0]
        while len(cyc) < n:
            cyc.append(succ[cyc[-1]])
        assert succ[cyc[-1]] == 0
        cycles.append(cyc)
    return solver.StatusName(st), cycles

def check(n, cycles, classes):
    seen = set()
    for c, cyc in enumerate(cycles):
        assert len(set(cyc)) == n
        es = {frozenset((cyc[i], cyc[(i + 1) % n])) for i in range(n)}
        assert not (seen & es); seen |= es
        for e in classes[c]: assert frozenset(e) in es
        for d, cl in enumerate(classes):
            if d != c:
                for e in cl: assert frozenset(e) not in es
    assert len(seen) == n * (n - 1) // 2
    return True

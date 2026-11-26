"""Exact solvers: (1) one-vertex Hilton step (random, CP-SAT) for generating instances;
(2) the two-vertex extension problem (TVL) solved directly with CP-SAT, with the result
verified at graph level; (3) the Stage-Z flow network solved with networkx."""
import random
import networkx as nx
from ortools.sat.python import cp_model
from lf import components, edges_by_colour, is_linear_forest, pvec, tvl_demands

def one_vertex_step(m, n, col, rng, targets=None, timeout=10.0):
    """Add vertex m to K_m. targets[i] = max allowed p'_i (default K-1). Random objective."""
    K = 2 * n + 1 - m
    p = pvec(m, n, col)
    if targets is None:
        targets = [K - 1] * n
    E = edges_by_colour(m, n, col)
    deg = [[0] * m for _ in range(n)]
    for i in range(n):
        for u, v in E[i]:
            deg[i][u] += 1; deg[i][v] += 1
    mdl = cp_model.CpModel()
    b = {}
    for v in range(m):
        for i in range(n):
            if deg[i][v] <= 1:
                b[v, i] = mdl.NewBoolVar("")
        mdl.Add(sum(b[v, i] for i in range(n) if (v, i) in b) == 1)
    for i in range(n):
        s = sum(b[v, i] for v in range(m) if (v, i) in b)
        mdl.Add(s <= 2)
        mdl.Add(p[i] + 1 - s <= targets[i])
        for (u, w) in components(m, E[i]):
            if u != w:
                mdl.Add(b[u, i] + b[w, i] <= 1)
    mdl.Maximize(sum(rng.randint(0, 100) * x for x in b.values()))
    sol = cp_model.CpSolver(); sol.parameters.max_time_in_seconds = timeout
    sol.parameters.random_seed = rng.randint(0, 10**6)
    st = sol.Solve(mdl)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return None
    new = dict(col)
    for (v, i), x in b.items():
        if sol.Value(x):
            new[(v, m)] = i
    return new

def tvl_cpsat(m, n, col, U, c, timeout=20.0, verify=True):
    """Directly search for a two-vertex extension (x=m, y=m+1, xy in colour c).
    Returns new colouring or None if infeasible (status reported)."""
    K = 2 * n + 1 - m
    p = pvec(m, n, col)
    d = tvl_demands(p, K, U, c)
    E = edges_by_colour(m, n, col)
    deg = [[0] * m for _ in range(n)]
    for i in range(n):
        for u, v in E[i]:
            deg[i][u] += 1; deg[i][v] += 1
    mdl = cp_model.CpModel()
    bx, by = {}, {}
    for v in range(m):
        for i in range(n):
            if deg[i][v] <= 1:
                bx[v, i] = mdl.NewBoolVar(""); by[v, i] = mdl.NewBoolVar("")
                mdl.Add(bx[v, i] + by[v, i] <= 2 - deg[i][v])
        mdl.Add(sum(bx[v, i] for i in range(n) if (v, i) in bx) == 1)
        mdl.Add(sum(by[v, i] for i in range(n) if (v, i) in by) == 1)
    for i in range(n):
        cap = 1 if i == c else 2
        sx = sum(bx[v, i] for v in range(m) if (v, i) in bx)
        sy = sum(by[v, i] for v in range(m) if (v, i) in by)
        mdl.Add(sx <= cap); mdl.Add(sy <= cap)
        mdl.Add(sx + sy >= d[i])
        dbl = []
        for (u, w) in components(m, E[i]):
            if u != w:
                mdl.Add(bx[u, i] + bx[w, i] <= 1)
                mdl.Add(by[u, i] + by[w, i] <= 1)
                z1 = mdl.NewBoolVar(""); z2 = mdl.NewBoolVar("")
                mdl.AddBoolAnd([bx[u, i], by[w, i]]).OnlyEnforceIf(z1)
                mdl.AddBoolOr([bx[u, i].Not(), by[w, i].Not()]).OnlyEnforceIf(z1.Not())
                mdl.AddBoolAnd([by[u, i], bx[w, i]]).OnlyEnforceIf(z2)
                mdl.AddBoolOr([by[u, i].Not(), bx[w, i].Not()]).OnlyEnforceIf(z2.Not())
                dbl += [z1, z2]
            else:
                z = mdl.NewBoolVar("")
                mdl.AddBoolAnd([bx[u, i], by[u, i]]).OnlyEnforceIf(z)
                mdl.AddBoolOr([bx[u, i].Not(), by[u, i].Not()]).OnlyEnforceIf(z.Not())
                dbl.append(z)
        mdl.Add(sum(dbl) <= (0 if i == c else 1))
    sol = cp_model.CpSolver(); sol.parameters.max_time_in_seconds = timeout
    st = sol.Solve(mdl)
    if st == cp_model.INFEASIBLE:
        return None
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise RuntimeError("timeout")
    new = dict(col)
    x, y = m, m + 1
    for (v, i), z in bx.items():
        if sol.Value(z): new[(v, x)] = i
    for (v, i), z in by.items():
        if sol.Value(z): new[(v, y)] = i
    new[(x, y)] = c
    if verify:
        E2 = edges_by_colour(m + 2, n, new)
        assert all(is_linear_forest(m + 2, E2[i]) for i in range(n)), "graph-level check failed"
        p2 = [m + 2 - len(E2[i]) for i in range(n)]
        for i in range(n):
            lim = K - 3 if (i in U and i != c) else K - 2
            assert p2[i] <= lim, (i, p2[i], lim)
    return new

def stageZ_flow(m, n, col, U, c):
    """Feasibility of the Stage-Z network with lower bounds (standard reduction)."""
    K = 2 * n + 1 - m
    p = pvec(m, n, col)
    d = tvl_demands(p, K, U, c)
    E = edges_by_colour(m, n, col)
    G = nx.DiGraph()
    # arcs with lower bounds -> excess bookkeeping
    excess = {}
    def arc(a, b, lo, hi):
        if hi - lo > 0:
            if G.has_edge(a, b): G[a][b]["capacity"] += hi - lo
            else: G.add_edge(a, b, capacity=hi - lo)
        if lo:
            excess[b] = excess.get(b, 0) + lo
            excess[a] = excess.get(a, 0) - lo
    for v in range(m):
        arc("s", ("v", v), 2, 2)
    for i in range(n):
        for k, (u, w) in enumerate(components(m, E[i])):
            C = ("C", i, k)
            if u == w:
                arc(("v", u), C, 0, 2)
            else:
                arc(("v", u), C, 0, 1); arc(("v", w), C, 0, 1)
            arc(C, ("g", i), 0, 1)
            arc(C, ("h", i), 0, 1)
        if i != c:
            arc(("h", i), ("g", i), 0, 1)
        arc(("g", i), "t", d[i], 2 if i == c else 4)
    arc("t", "s", 0, 10**6)
    S, T = "SS", "TT"; need = 0
    for node, e in excess.items():
        if e > 0: G.add_edge(S, node, capacity=e); need += e
        elif e < 0: G.add_edge(node, T, capacity=-e)
    if need == 0: return True
    val, _ = nx.maximum_flow(G, S, T)
    return val == need

"""a37lib.py: audit A37 -- independent helpers (own graph6 decoder, own 3-connectivity test,
own CP-SAT path-decomposition model, own decomposition checker).  Nothing here imports the
session's scripts.
"""
import itertools

from ortools.sat.python import cp_model


# ---------------------------------------------------------------- graph6 / basic graph helpers
def g6_decode(s):
    """Return (n, set of frozenset edges) for a graph6 string (n < 63)."""
    s = s.strip()
    data = [ord(c) - 63 for c in s]
    n = data[0]
    bits = []
    for d in data[1:]:
        for i in range(5, -1, -1):
            bits.append((d >> i) & 1)
    E = set()
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                E.add(frozenset((i, j)))
            k += 1
    return n, E


def adjacency(n, E):
    A = [set() for _ in range(n)]
    for e in E:
        a, b = tuple(e)
        A[a].add(b)
        A[b].add(a)
    return A


def connected_without(n, A, removed):
    vs = [v for v in range(n) if v not in removed]
    if not vs:
        return True
    seen = {vs[0]}
    st = [vs[0]]
    while st:
        u = st.pop()
        for w in A[u]:
            if w not in removed and w not in seen:
                seen.add(w)
                st.append(w)
    return len(seen) == len(vs)


def kconn(n, A, k):
    """True iff the graph is k-connected (n >= k+1, no separating set of size < k)."""
    if n < k + 1:
        return False
    for s in range(k):
        for X in itertools.combinations(range(n), s):
            if not connected_without(n, A, set(X)):
                return False
    return True


def t2_instances(n, E):
    """The (z, r) orientations at which (T2) is posed: exactly two even vertices, adjacent."""
    A = adjacency(n, E)
    ev = [v for v in range(n) if len(A[v]) % 2 == 0]
    if len(ev) != 2 or ev[1] not in A[ev[0]]:
        return []
    return [(ev[0], ev[1]), (ev[1], ev[0])]


def delete_vertex(E, z):
    return {e for e in E if z not in e}


# ---------------------------------------------------------------- independent checker
def check_decomp(E, paths, maxpaths=None, r=None, minends=0):
    """Check that paths (vertex lists) partition the edge set E into paths of positive length;
    optionally at most maxpaths paths and at least minends ends at r.  Raises on failure."""
    used = set()
    ends = {}
    for P in paths:
        assert len(P) >= 2, ("short", P)
        assert len(set(P)) == len(P), ("repeat", P)
        for a, b in zip(P, P[1:]):
            e = frozenset((a, b))
            assert e in E, ("not an edge", P, a, b)
            assert e not in used, ("edge twice", e)
            used.add(e)
        ends[P[0]] = ends.get(P[0], 0) + 1
        ends[P[-1]] = ends.get(P[-1], 0) + 1
    assert used == set(E), ("uncovered", set(E) - used)
    if maxpaths is not None:
        assert len(paths) <= maxpaths, ("too many paths", len(paths), maxpaths)
    if r is not None:
        assert ends.get(r, 0) >= minends, ("ends at r", ends.get(r, 0), minends)
    return ends


# ---------------------------------------------------------------- CP-SAT model
def cpsat_decomp(E, P, r=None, minends=0, time_limit=60.0, workers=1):
    """Decompose the edge set E into at most P paths (each a slot) with at least `minends` ends
    at r.  Returns ('FEAS', paths) / ('INFEAS', None) / ('UNKNOWN', None).

    Model: x[e,s] edge e in slot s; each edge in exactly one slot.  Each edge used in a slot is
    oriented (f[u->v,s] + f[v->u,s] = x[e,s]); in- and out-degree <= 1 per vertex per slot;
    start/finish indicators with start - finish = out - in; a used slot has exactly one start and
    one finish; positions pos[v,s] with pos[v] = pos[u] + 1 along every oriented edge forbid
    directed cycles.  Hence every used slot is exactly one path of positive length."""
    E = [tuple(sorted(e)) for e in E]
    V = sorted({v for e in E for v in e})
    nV = len(V)
    m = cp_model.CpModel()
    x = {(e, s): m.NewBoolVar("") for e in E for s in range(P)}
    f = {}
    for (a, b) in E:
        for s in range(P):
            f[(a, b, s)] = m.NewBoolVar("")
            f[(b, a, s)] = m.NewBoolVar("")
            m.Add(f[(a, b, s)] + f[(b, a, s)] == x[((a, b), s)])
    for e in E:
        m.AddExactlyOne(x[(e, s)] for s in range(P))
    used = [m.NewBoolVar("") for s in range(P)]
    nb = {v: [] for v in V}
    for (a, b) in E:
        nb[a].append(b)
        nb[b].append(a)
    st = {}
    fi = {}
    for s in range(P):
        for e in E:
            m.AddImplication(x[(e, s)], used[s])
        m.AddBoolOr([x[(e, s)] for e in E]).OnlyEnforceIf(used[s])
        pos = {v: m.NewIntVar(0, nV, "") for v in V}
        for v in V:
            ins = [f[(u, v, s)] for u in nb[v]]
            outs = [f[(v, u, s)] for u in nb[v]]
            m.Add(sum(ins) <= 1)
            m.Add(sum(outs) <= 1)
            st[(v, s)] = m.NewBoolVar("")
            fi[(v, s)] = m.NewBoolVar("")
            m.Add(st[(v, s)] - fi[(v, s)] == sum(outs) - sum(ins))
            m.Add(st[(v, s)] + fi[(v, s)] <= 1)
        m.Add(sum(st[(v, s)] for v in V) == used[s])
        m.Add(sum(fi[(v, s)] for v in V) == used[s])
        for (a, b) in E:
            m.Add(pos[b] == pos[a] + 1).OnlyEnforceIf(f[(a, b, s)])
            m.Add(pos[a] == pos[b] + 1).OnlyEnforceIf(f[(b, a, s)])
    for s in range(P - 1):
        m.AddImplication(used[s + 1], used[s])
    if r is not None and minends > 0:
        m.Add(sum(st[(r, s)] + fi[(r, s)] for s in range(P)) >= minends)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = workers
    res = solver.Solve(m)
    if res in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        paths = []
        for s in range(P):
            if not solver.Value(used[s]):
                continue
            nxt = {}
            start = None
            for (a, b) in E:
                if solver.Value(f[(a, b, s)]):
                    nxt[a] = b
                if solver.Value(f[(b, a, s)]):
                    nxt[b] = a
            for v in V:
                if solver.Value(st[(v, s)]):
                    start = v
            path = [start]
            while path[-1] in nxt:
                path.append(nxt[path[-1]])
            paths.append(path)
        return "FEAS", paths
    if res == cp_model.INFEASIBLE:
        return "INFEAS", None
    return "UNKNOWN", None

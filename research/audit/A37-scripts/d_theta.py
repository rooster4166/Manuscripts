"""d_theta.py (audit A37, item 3d): exhaustive forest-base search, my own code, no oracle.

For J (graph6) and an orientation (z, r) with z, r the only even vertices:
  * every edge subset Phi of B = J - z that is a forest with odd set exactly N(z) (forest T-join);
  * every rooting (one root per component), split into r-a-root and r-a-child-with->=2-children;
  * M = J - {zv : v in N(z) - r} - Phi; EVERY Lovasz decomposition of M is enumerated (all
    vertices of M are odd, so every vertex ends exactly one path);
  * conditions (i) p(v) not in V(Q0(v)) for non-roots v, (ii) Q0(x) != Q0(y) for siblings.
Reports the number of bases in each mode; for one base with r a child (if any) the lift is executed
by my own code and checked as a (T2) decomposition; also a manual check of the base described in
Example 4.7 of the manuscript.
usage: python3 d_theta.py G6 z r
"""
import itertools
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from a37lib import adjacency, check_decomp, delete_vertex, g6_decode


def lovasz_all_odd(n, Eset):
    """All decompositions of the edge set Eset (on vertices 0..n-1, all of odd degree or
    degree 0) into paths with exactly one end at every vertex of positive degree."""
    A = adjacency(n, Eset)
    active = [v for v in range(n) if A[v]]
    assert all(len(A[v]) % 2 == 1 for v in active)
    out = []

    def paths_from(v, rem, ended):
        # simple paths from v in rem whose other end is a vertex with no end yet
        res = []

        def dfs(path, vis, used):
            u = path[-1]
            if len(path) >= 2 and u not in ended:
                res.append((list(path), set(used)))
            for w in sorted(A[u]):
                e = frozenset((u, w))
                if e in rem and e not in used and w not in vis:
                    path.append(w)
                    vis.add(w)
                    used.add(e)
                    dfs(path, vis, used)
                    path.pop()
                    vis.discard(w)
                    used.discard(e)
        dfs([v], {v}, set())
        return res

    def rec(rem, ended, acc):
        todo = [v for v in active if v not in ended]
        if not todo:
            if not rem:
                out.append(list(acc))
            return
        v = todo[0]
        for P, used in paths_from(v, rem, ended):
            u = P[-1]
            rec(rem - used, ended | {v, u}, acc + [P])
    rec(frozenset(Eset), frozenset(), [])
    return out


def forest_tjoins(Bedges, T):
    Bedges = sorted(Bedges, key=lambda e: sorted(e))
    T = set(T)
    res = []
    for mask in range(1 << len(Bedges)):
        F = [Bedges[i] for i in range(len(Bedges)) if mask >> i & 1]
        deg = {}
        for e in F:
            for v in e:
                deg[v] = deg.get(v, 0) + 1
        if {v for v, d in deg.items() if d % 2} != T:
            continue
        # forest test: union-find
        uf = {}

        def f(x):
            while uf.get(x, x) != x:
                x = uf[x]
            return x
        ok = True
        for e in F:
            a, b = tuple(e)
            ra, rb = f(a), f(b)
            if ra == rb:
                ok = False
                break
            uf[ra] = rb
        if ok:
            res.append(F)
    return res


def components(F):
    A = {}
    for e in F:
        a, b = tuple(e)
        A.setdefault(a, set()).add(b)
        A.setdefault(b, set()).add(a)
    seen, comps = set(), []
    for v in sorted(A):
        if v in seen:
            continue
        c, st = [], [v]
        seen.add(v)
        while st:
            u = st.pop()
            c.append(u)
            for w in A[u]:
                if w not in seen:
                    seen.add(w)
                    st.append(w)
        comps.append(sorted(c))
    return A, comps


def rootings(F):
    A, comps = components(F)
    for roots in itertools.product(*comps):
        par, order = {}, []
        for ro in roots:
            q = [ro]
            seen = {ro}
            for u in q:
                for w in sorted(A[u]):
                    if w not in seen:
                        seen.add(w)
                        par[w] = u
                        order.append(w)
                        q.append(w)
        yield roots, par, order


def is_base(D0, par):
    Q = {}
    for i, P in enumerate(D0):
        Q[P[0]] = i
        Q[P[-1]] = i
    for v, p in par.items():
        if p in D0[Q[v]]:
            return False
    kids = {}
    for v, p in par.items():
        kids.setdefault(p, []).append(v)
    for p, ch in kids.items():
        if len({Q[c] for c in ch}) < len(ch):
            return False
    return True


def my_lift(E, z, r, par, order, D0, n):
    """Own implementation: append p(v)v at v (BFS order = parents first), trim/drop z, split at r."""
    paths = [list(P) for P in D0]
    for v in order:
        hit = [P for P in paths if P[0] == v or P[-1] == v]
        assert len(hit) == 1
        P = hit[0]
        if P[0] == v:
            P.insert(0, par[v])
        else:
            P.append(par[v])
        assert len(set(P)) == len(P)
    zp = [P for P in paths if z in P]
    assert len(zp) == 1
    P = zp[0]
    if P[-1] == z:
        P.reverse()
    assert P[0] == z and P[1] == r
    if len(P) > 2:
        P.pop(0)
    else:
        paths.remove(P)
    B = delete_vertex(E, z)
    ends = check_decomp(B, paths)
    while ends.get(r, 0) < 3:
        Pi = [P for P in paths if r in P[1:-1]][0]
        k = Pi.index(r)
        paths.remove(Pi)
        paths += [Pi[:k + 1], Pi[k:]]
        ends = check_decomp(B, paths)
    check_decomp(B, paths, maxpaths=n // 2, r=r, minends=3)
    return paths


def main():
    g6, z, r = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    n, E = g6_decode(g6)
    A = adjacency(n, E)
    ev = [v for v in range(n) if len(A[v]) % 2 == 0]
    assert sorted(ev) == sorted((z, r)) and r in A[z]
    print("degrees", [len(A[v]) for v in range(n)], "N(z)", sorted(A[z]))
    B = delete_vertex(E, z)
    T = sorted(A[z])
    forests = forest_tjoins(B, T)
    print("forest T-joins:", len(forests))
    count = {"root": [0, 0], "child": [0, 0]}  # [rootings tried, bases found]
    child_example = None
    nlov = 0
    for F in forests:
        Mset = {e for e in E if not (z in e and (set(e) - {z}).pop() != r)} - set(F)
        D0s = lovasz_all_odd(n, Mset)
        nlov += len(D0s)
        for roots, par, order in rootings(F):
            kids_r = sum(1 for v in par if par[v] == r)
            if r in roots:
                mode = "root"
            elif kids_r >= 2:
                mode = "child"
            else:
                continue
            count[mode][0] += 1
            for D0 in D0s:
                if is_base(D0, par):
                    count[mode][1] += 1
                    if mode == "child" and child_example is None:
                        child_example = (F, par, order, D0)
    print("Lovasz decompositions enumerated (summed over forests):", nlov)
    print("r a root : rootings", count["root"][0], " (rooting, D0) bases", count["root"][1])
    print("r a child: rootings", count["child"][0], " (rooting, D0) bases", count["child"][1])
    if child_example:
        F, par, order, D0 = child_example
        paths = my_lift(E, z, r, par, order, D0, n)
        print("example child base: Phi", [sorted(e) for e in F], "par", par)
        print("  D0", D0)
        print("  lift (verified (T2) by own checker):", paths)


if __name__ == "__main__":
    main()

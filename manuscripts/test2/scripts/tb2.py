"""tb2.py: the (T2) forest base and its lift (test2 session).

Setting: J with exactly two even vertices z, r, adjacent; B = J - z; T = N_J(z) (r included).
Data: a forest T-join Phi of B, rooted, with r a root of its component.
Base graph: M = J - {zv : v in N(z) - r} - E(Phi).  M has no even vertex and z is a leaf at r.
Base: a Lovasz decomposition D0 of M (one end at every vertex) with
   (i)  p(v) not in V(Q0(v)) for every non-root vertex v of Phi,
   (ii) Q0(x) != Q0(y) for distinct siblings x, y.
Lift: append each parent edge p(v)v at the end v of its path (parent-first order), then delete z
(trim it, or drop the path zr and split a path at r).  The result is checked to be a (T2)
decomposition of B: at most n/2 paths with at least three ends at r.

The base is searched with tools/route_ext.c, query C, with r_v = {v, p(v)} at the children
(this is exactly (i) and (ii)), profile all ones.  Every base found is lifted and the lift is
verified here, independently of the oracle.

Tiers, in order (the first that succeeds is reported):
  M  : Phi a perfect matching of J[N(z)] (triangle data), every matching and orientation;
  S  : Phi the T-join of a spanning tree of B (BFS trees from every vertex, plus random trees),
       every rooting with r a root (other components: every root);
  X  : every forest T-join of B (spanning-tree T-join + cycle space, when its dimension is at
       most XDIM), every rooting.
Output per instance:  g6 z r dz dr tier dPhi(r) nbase_queries  [witness]
  tier is M, S, X, ABSENT (exhaustive over all forest T-joins and rootings) or UNDEC.
usage: python3 tb2.py ORACLE [budget] [xdim] < instances   (lines 'g6 z r ...' as printed by t2.c)
"""
import itertools
import random
import subprocess
import sys

import networkx as nx

XDIM = 14


def run_oracle(oracle, lines):
    if not lines:
        return []
    p = subprocess.run([oracle], input="\n".join(lines) + "\n", capture_output=True, text=True)
    out = p.stdout.strip().split("\n")
    assert len(out) == len(lines), (len(out), len(lines))
    return out


def perfect_matchings(vs, J):
    if not vs:
        yield []
        return
    a = vs[0]
    for b in vs[1:]:
        if J.has_edge(a, b):
            for pm in perfect_matchings([v for v in vs[1:] if v != b], J):
                yield [(a, b)] + pm


def base_graph(J, z, r, phi):
    M = J.copy()
    M.remove_edges_from([(z, v) for v in J[z] if v != r])
    M.remove_edges_from(phi)
    return M


def rootings(phi, r, cap):
    """Parent maps of the forest phi with r a root; every choice of root in the other components."""
    F = nx.Graph(list(phi))
    comps = [sorted(c) for c in nx.connected_components(F)]
    choices = [[r] if r in c else c for c in comps]
    out = []
    for roots in itertools.product(*choices):
        par, order = {}, []
        for c, ro in zip(comps, roots):
            seen = {ro}
            q = [ro]
            for u in q:
                for v in sorted(F[u]):
                    if v not in seen:
                        seen.add(v)
                        par[v] = u
                        order.append(v)
                        q.append(v)
        out.append((par, order))
        if len(out) >= cap:
            break
    return out


def query_line(M, n, par, budget, seed):
    E = list(M.edges())
    b = [1] * n
    masks = [(1 << v) | ((1 << par[v]) if v in par else 0) for v in range(n)]
    flag = "WCB" if budget else "WC"
    s = f"{flag} {n} {len(E)} " + " ".join(f"{u} {v}" for u, v in E) + " " + \
        " ".join(map(str, b)) + " " + " ".join(map(str, masks))
    if budget:
        s += f" {seed} {budget}"
    return s


def parse_paths(line):
    parts = line.split("|")[1:]
    return [list(map(int, p.split())) for p in parts if p.strip()]


def check_base(M, n, par, D0):
    used = set()
    ends = [0] * n
    for P in D0:
        assert len(P) >= 2 and len(set(P)) == len(P)
        for a, b in zip(P, P[1:]):
            assert M.has_edge(a, b)
            e = frozenset((a, b))
            assert e not in used
            used.add(e)
        ends[P[0]] += 1
        ends[P[-1]] += 1
    assert len(used) == M.number_of_edges()
    assert all(ends[v] == M.degree(v) % 2 for v in range(n)) and all(e == 1 for e in ends)
    Q = {}
    for P in D0:
        Q[P[0]] = P
        Q[P[-1]] = P
    for v, p in par.items():
        assert p not in Q[v], ("(i)", v, p)
    for x in par:
        for y in par:
            if x < y and par[x] == par[y]:
                assert Q[x] is not Q[y], ("(ii)", x, y)


def lift(J, z, r, par, order, D0):
    paths = [list(P) for P in D0]
    for v in order:
        p = par[v]
        idx = [i for i, P in enumerate(paths) if P[0] == v or P[-1] == v]
        assert len(idx) == 1, ("child end", v)
        P = paths[idx[0]]
        if P[0] == v:
            P.insert(0, p)
        else:
            P.append(p)
        assert len(set(P)) == len(P), ("append", v, p)
    i = [i for i, P in enumerate(paths) if z in P]
    assert len(i) == 1
    i = i[0]
    P = paths[i]
    if P[-1] == z:
        P.reverse()
    assert P[0] == z and P[1] == r
    if len(P) >= 3:
        paths[i] = P[1:]
    else:
        del paths[i]
    er = sum((P[0] == r) + (P[-1] == r) for P in paths)
    while er < 3:
        j = [j for j, P in enumerate(paths) if r in P[1:-1]][0]
        P = paths[j]
        k = P.index(r)
        paths[j:j + 1] = [P[:k + 1], P[k:]]
        er += 2
    return paths


def verify_test2(J, z, r, paths):
    B = J.copy()
    B.remove_node(z)
    n = J.number_of_nodes()
    used = set()
    er = 0
    for P in paths:
        assert len(P) >= 2 and len(set(P)) == len(P)
        for a, b in zip(P, P[1:]):
            assert B.has_edge(a, b)
            e = frozenset((a, b))
            assert e not in used
            used.add(e)
        er += (P[0] == r) + (P[-1] == r)
    assert len(used) == B.number_of_edges()
    assert len(paths) <= n // 2, (len(paths), n)
    assert er >= 3
    return True


def try_data(oracle, J, z, r, n, datas, budget, seed=7):
    """datas: list of (phi, par, order). Returns (found, witness, undecided)."""
    lines, meta = [], []
    for phi, par, order in datas:
        M = base_graph(J, z, r, phi)
        assert all(M.degree(v) % 2 == 1 for v in range(n)), "M not all-odd"
        lines.append(query_line(M, n, par, budget, seed))
        meta.append((phi, par, order, M))
    out = run_oracle(oracle, lines)
    und = 0
    for o, (phi, par, order, M) in zip(out, meta):
        if o.startswith("1"):
            D0 = parse_paths(o)
            check_base(M, n, par, D0)
            paths = lift(J, z, r, par, order, D0)
            verify_test2(J, z, r, paths)
            return True, (phi, par, D0, paths), 0
        if o.startswith("2"):
            und += 1
    return False, None, und


def tjoin_in_tree(S, T):
    Tset = set(T)
    out = []
    for comp in nx.connected_components(S):
        St = S.subgraph(comp)
        root = min(comp)
        parent = {root: None}
        order = [root]
        for u in order:
            for v in sorted(St[u]):
                if v not in parent:
                    parent[v] = u
                    order.append(v)
        cnt = {u: int(u in Tset) for u in comp}
        for u in reversed(order):
            if parent[u] is not None:
                if cnt[u] % 2 == 1:
                    out.append((parent[u], u))
                cnt[parent[u]] += cnt[u]
    return out


def bfs_tree(H, s):
    S = nx.Graph()
    S.add_nodes_from(H)
    seen = {s}
    q = [s]
    for u in q:
        for v in sorted(H[u]):
            if v not in seen:
                seen.add(v)
                S.add_edge(u, v)
                q.append(v)
    return S


def random_tree(H, rng):
    E = list(H.edges())
    rng.shuffle(E)
    S = nx.Graph()
    S.add_nodes_from(H)
    uf = {v: v for v in H}

    def f(x):
        while uf[x] != x:
            uf[x] = uf[uf[x]]
            x = uf[x]
        return x
    for u, v in E:
        a, b = f(u), f(v)
        if a != b:
            uf[a] = b
            S.add_edge(u, v)
    return S


def norm(phi):
    return frozenset(frozenset(e) for e in phi)


def process(oracle, J, z, r, budget, xdim, rng):
    n = J.number_of_nodes()
    B = J.copy()
    B.remove_node(z)
    T = sorted(J[z])
    nq = 0
    und = 0
    # tier M: perfect matchings of J[N(z)]
    datas = []
    for pm in perfect_matchings(T, J):
        datas.extend((pm, par, order) for par, order in rootings(pm, r, 10 ** 6))
    if datas:
        nq += len(datas)
        ok, wit, u = try_data(oracle, J, z, r, n, datas, budget)
        und += u
        if ok:
            return "M", wit, nq, und
    # tier S: spanning-tree T-joins
    seen = set()
    datas = []
    trees = [bfs_tree(B, s) for s in sorted(B)] + [random_tree(B, rng) for _ in range(20)]
    for S in trees:
        phi = tjoin_in_tree(S, T)
        key = norm(phi)
        if key in seen:
            continue
        seen.add(key)
        datas.extend((phi, par, order) for par, order in rootings(phi, r, 64))
    nq += len(datas)
    ok, wit, u = try_data(oracle, J, z, r, n, datas, budget)
    und += u
    if ok:
        return "S", wit, nq, und
    # tier X: all forest T-joins
    E = sorted(tuple(sorted(e)) for e in B.edges())
    idx = {e: i for i, e in enumerate(E)}
    cyc = []
    for c in nx.cycle_basis(B):
        vec = 0
        for a, b in zip(c, c[1:] + c[:1]):
            vec ^= 1 << idx[tuple(sorted((a, b)))]
        cyc.append(vec)
    if len(cyc) > xdim:
        return "UNDEC", None, nq, und
    phi0 = 0
    for e in tjoin_in_tree(bfs_tree(B, min(B)), T):
        phi0 |= 1 << idx[tuple(sorted(e))]
    datas = []
    for k in range(len(cyc) + 1):
        for comb in itertools.combinations(cyc, k):
            v = phi0
            for c in comb:
                v ^= c
            phi = [E[i] for i in range(len(E)) if v >> i & 1]
            if not nx.is_forest(nx.Graph(phi)) or norm(phi) in seen:
                continue
            seen.add(norm(phi))
            datas.extend((phi, par, order) for par, order in rootings(phi, r, 10 ** 6))
    nq += len(datas)
    ok, wit, u = try_data(oracle, J, z, r, n, datas, budget)
    und += u
    if ok:
        return "X", wit, nq, und
    return ("ABSENT" if und == 0 else "UNDEC"), None, nq, und


def main():
    oracle = sys.argv[1]
    budget = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    xdim = int(sys.argv[3]) if len(sys.argv) > 3 else XDIM
    rng = random.Random(1)
    from collections import Counter
    stats = Counter()
    for line in sys.stdin:
        if not line.strip():
            continue
        g6, tail = line.split(None, 1)
        f = tail.split("|")[0].split()
        z, r = int(f[0]), int(f[1])
        J = nx.from_graph6_bytes(g6.encode())
        tier, wit, nq, und = process(oracle, J, z, r, budget, xdim, rng)
        dphi = "-"
        if wit:
            phi = wit[0]
            dphi = sum(1 for e in phi if r in e)
        stats[tier] += 1
        if wit:
            stats[("dPhi(r)", dphi)] += 1
        print(g6, z, r, J.degree(z), J.degree(r), tier, dphi, nq, und, flush=True)
    print("SUMMARY", dict(stats), file=sys.stderr)


if __name__ == "__main__":
    main()

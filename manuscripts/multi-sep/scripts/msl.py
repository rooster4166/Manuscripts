"""multi-sep library: graphs, Lovasz decompositions, Fan transfers, separation checks.

Graphs: dict v -> set of neighbours (vertices are ints).  Decompositions: lists of paths, each a
list of vertices.  Pure Python; used for small exploratory experiments.
"""
import itertools
import random


def edges(K):
    return [(u, v) for u in K for v in K[u] if u < v]


def deg(K, v):
    return len(K[v])


def copy(K):
    return {v: set(N) for v, N in K.items()}


def ends(D, V):
    b = {v: 0 for v in V}
    for P in D:
        b[P[0]] += 1
        b[P[-1]] += 1
    return b


def is_decomp(K, D, b=None):
    used = set()
    for P in D:
        if len(P) < 2 or len(set(P)) != len(P):
            return False
        for x, y in zip(P, P[1:]):
            if y not in K[x]:
                return False
            e = (min(x, y), max(x, y))
            if e in used:
                return False
            used.add(e)
    if len(used) != len(edges(K)):
        return False
    if b is not None:
        bb = ends(D, K)
        if any(bb[v] != b[v] for v in K):
            return False
    return True


def lovasz_profile(K):
    return {v: len(K[v]) % 2 for v in K}


def separates(D, pairs):
    for P in D:
        S = set(P)
        for s, t in pairs:
            if s in S and t in S:
                return False
    return True


def dist(K, s):
    d = {s: 0}
    fr = [s]
    while fr:
        nf = []
        for x in fr:
            for y in K[x]:
                if y not in d:
                    d[y] = d[x] + 1
                    nf.append(y)
        fr = nf
    return d


def all_decomps(K, b, limit=None, pairs=None):
    """Enumerate path decompositions of K with ends b (b(v) in {0,1,2}).  If pairs is given, only
    separating ones (pruned during the search)."""
    K = copy(K)
    b = dict(b)
    out = []
    bad = {}
    if pairs:
        for s, t in pairs:
            bad.setdefault(s, set()).add(t)
            bad.setdefault(t, set()).add(s)
    rem = {v: set(K[v]) for v in K}
    nedges = [sum(len(x) for x in rem.values()) // 2]
    cur = []

    def ok():
        for v in rem:
            d = len(rem[v])
            if b[v] > d or (d - b[v]) % 2:
                return False
        return True

    def solve():
        if limit and len(out) >= limit:
            return
        if nedges[0] == 0:
            if all(b[v] == 0 for v in b):
                out.append([list(P) for P in cur])
            return
        if not ok():
            return
        cand = [v for v in rem if b[v] > 0 and rem[v]]
        if not cand:
            return
        v = min(cand)
        path = [v]
        vis = {v}
        b[v] -= 1
        extend(path, vis)
        b[v] += 1

    def extend(path, vis):
        x = path[-1]
        for y in sorted(rem[x]):
            if y in vis:
                continue
            if pairs and any(w in vis for w in bad.get(y, ())):
                continue
            rem[x].discard(y); rem[y].discard(x); nedges[0] -= 1
            path.append(y); vis.add(y)
            if b[y] > 0:
                b[y] -= 1
                cur.append(list(path))
                solve()
                cur.pop()
                b[y] += 1
            extend(path, vis)
            path.pop(); vis.discard(y)
            rem[x].add(y); rem[y].add(x); nedges[0] += 1
            if limit and len(out) >= limit:
                return

    solve()
    return out


def fan_chains(D, t, u, K):
    """All Fan chains for adding edge tu (tu not in K) moving an end from t to u.
    A chain: list of (x_i, path index, orientation) and final (x_k, path index) of a path ending at
    x_k avoiding u.  Returns list of chains as (steps, final)."""
    # path-ends at x: (idx, side) with side 0 = P[0] == x, side 1 = P[-1] == x
    at = {}
    for i, P in enumerate(D):
        at.setdefault(P[0], []).append((i, 0))
        at.setdefault(P[-1], []).append((i, 1))
    res = []

    def pi(i, side):
        P = D[i] if side == 0 else D[i][::-1]
        j = P.index(u)
        return P[j - 1]

    def rec(x, seen, steps):
        for (i, side) in at.get(x, []):
            P = D[i]
            if u not in P:
                res.append((list(steps), (x, i, side)))
            else:
                y = pi(i, side)
                if y not in seen:
                    steps.append((x, i, side))
                    seen.add(y)
                    rec(y, seen, steps)
                    seen.discard(y)
                    steps.pop()

    rec(t, {t}, [])
    return res


def fan_exec(D, chain, u):
    """Execute a chain on a copy of D; returns the new decomposition (list of paths)."""
    D = [list(P) for P in D]
    steps, (xk, ik, sk) = chain
    for (x, i, side) in steps:
        P = D[i]
        if P[0] != x:
            P = P[::-1]
        assert P[0] == x
        j = P.index(u)
        # P = x ... y u ... ; new = y ... x u ...
        newP = P[:j][::-1] + P[j:]
        D[i] = newP
    P = D[ik]
    if P[-1] == xk:
        P = P + [u]
    else:
        assert P[0] == xk
        P = [u] + P
    D[ik] = P
    return D


def random_odd_graph(n, p, rng):
    K = {v: set() for v in range(n)}
    for u in range(n):
        for v in range(u + 1, n):
            if rng.random() < p:
                K[u].add(v); K[v].add(u)
    ev = [v for v in K if len(K[v]) % 2 == 0]
    rng.shuffle(ev)
    while len(ev) >= 2:
        x, y = ev.pop(), ev.pop()
        if y in K[x]:
            K[x].discard(y); K[y].discard(x)
        else:
            K[x].add(y); K[y].add(x)
    if any(len(K[v]) % 2 == 0 for v in K):
        return None
    return K


def far_pairs(K, rng, mind=3, tries=100, perfect_only=False):
    D = {v: dist(K, v) for v in K}
    V = list(K)
    best = []
    for _ in range(tries):
        rng.shuffle(V)
        used, N = set(), []
        for u in V:
            if u in used:
                continue
            cand = [w for w in V if w not in used and w != u and D[u].get(w, 99) >= mind]
            if cand:
                w = rng.choice(cand)
                N.append((u, w)); used |= {u, w}
        if len(N) > len(best):
            best = N
        if 2 * len(best) == len(V):
            break
    if perfect_only and 2 * len(best) != len(V):
        return None
    return best


def random_cubic(n, rng, tries=1000):
    for _ in range(tries):
        pts = [v for v in range(n) for _ in range(3)]
        rng.shuffle(pts)
        K = {v: set() for v in range(n)}
        ok = True
        for i in range(0, len(pts), 2):
            a, c = pts[i], pts[i + 1]
            if a == c or c in K[a]:
                ok = False; break
            K[a].add(c); K[c].add(a)
        if ok:
            return K
    return None

"""A11: small exact solvers for path partitions (own code, DFS with memoisation).

realise(G, beta)      -> a partition of G with exactly beta(v) ends at every v, or None
floor_with_end(G, y)  -> True iff G has a partition into <= floor(N/2) paths with an end at y
Graphs are dicts vertex -> set of neighbours (simple, undirected).
"""
from functools import lru_cache
import itertools


def _key(u, v):
    return (u, v) if u < v else (v, u)


def realise(G, beta, want_partition=False):
    V = sorted(G)
    idx = {v: i for i, v in enumerate(V)}
    n = len(V)
    edges = sorted({_key(idx[u], idx[w]) for u in G for w in G[u]})
    m = len(edges)
    eid = {e: i for i, e in enumerate(edges)}
    inc = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        inc[a].append((i, b))
        inc[b].append((i, a))
    beta0 = tuple(beta.get(v, 0) for v in V)
    full = (1 << m) - 1

    def deg(mask, v):
        return sum(1 for i, _ in inc[v] if mask >> i & 1)

    def ok(mask, rem):
        if any(r < 0 for r in rem):
            return False
        for v in range(n):
            d = deg(mask, v)
            if rem[v] > d or (rem[v] - d) % 2:
                return False
        # every component of remaining edges must contain a vertex with rem > 0
        seen = 0
        for v in range(n):
            if seen >> v & 1 or deg(mask, v) == 0:
                continue
            stack = [v]; seen |= 1 << v; has = False
            while stack:
                w = stack.pop()
                if rem[w] > 0:
                    has = True
                for i, z in inc[w]:
                    if mask >> i & 1 and not seen >> z & 1:
                        seen |= 1 << z
                        stack.append(z)
            if not has:
                return False
        return True

    @lru_cache(maxsize=None)
    def solve(mask, rem):
        if mask == 0:
            return () if all(r == 0 for r in rem) else None
        if not ok(mask, rem):
            return None
        s = min((v for v in range(n) if rem[v] > 0), key=lambda v: (deg(mask, v), v))
        # build a path from s
        res = [None]

        def ext(c, visited, mask2, path):
            if res[0] is not None:
                return
            if c != s and rem[c] > 0:
                r2 = list(rem); r2[s] -= 1; r2[c] -= 1
                sub = solve(mask2, tuple(r2))
                if sub is not None:
                    res[0] = (tuple(path),) + sub
                    return
            for i, z in inc[c]:
                if mask2 >> i & 1 and not visited >> z & 1:
                    ext(z, visited | 1 << z, mask2 & ~(1 << i), path + [z])
                    if res[0] is not None:
                        return

        ext(s, 1 << s, mask, [s])
        return res[0]

    out = solve(full, beta0)
    if out is None:
        return None
    return [tuple(V[i] for i in p) for p in out]


def check_partition(G, P, beta=None):
    used = set()
    ends = {v: 0 for v in G}
    for p in P:
        if len(p) < 2 or len(set(p)) != len(p):
            return False
        for a, b in zip(p, p[1:]):
            if b not in G[a]:
                return False
            e = _key(a, b)
            if e in used:
                return False
            used.add(e)
        ends[p[0]] += 1
        ends[p[-1]] += 1
    alle = {_key(a, b) for a in G for b in G[a]}
    if used != alle:
        return False
    if beta is not None and any(ends[v] != beta.get(v, 0) for v in G):
        return False
    return True


def floor_with_end(G, y, budget=None):
    """Some partition into <= budget paths (default floor(N/2)) with b(y) >= 1.
    Any such partition has an end vector >= base (1 on odd, 2 at y if y even, else 1); we
    enumerate all end vectors between base and the budget (adding ends in pairs) and call realise."""
    N = len(G)
    if budget is None:
        budget = N // 2
    deg = {v: len(G[v]) for v in G}
    base = {v: (deg[v] % 2) for v in G}
    if base[y] == 0:
        base[y] = 2
    slack = 2 * budget - sum(base.values())
    if slack < 0:
        return None
    verts = [v for v in G if deg[v] > 0]
    for extra in range(0, slack // 2 + 1):
        for combo in itertools.combinations_with_replacement(verts, extra):
            beta = dict(base)
            for w in combo:
                beta[w] += 2
            if any(beta[w] > deg[w] for w in G):
                continue
            P = realise(G, beta)
            if P is not None:
                return P
    return None

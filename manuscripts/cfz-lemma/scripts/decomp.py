"""Small exact path-decomposition oracle (pure Python, bitmask DFS).

paths_at_most(edges, k): True iff the simple graph with the given edge list
partitions into at most k vertex-simple paths.  The search picks the lowest
uncovered edge, enumerates every simple path through it in the uncovered
subgraph (left arm x right arm), and recurses.  Pruning: edge count
<= k*(n-1) and number of odd-degree vertices <= 2k.
"""
from functools import lru_cache

def paths_at_most(edges, k, want_solution=False):
    verts = sorted({v for e in edges for v in e})
    idx = {v: i for i, v in enumerate(verts)}
    n = len(verts)
    E = [(idx[a], idx[b]) for a, b in edges]
    m = len(E)
    adj = [[] for _ in range(n)]
    for j, (a, b) in enumerate(E):
        adj[a].append((b, j)); adj[b].append((a, j))
    full = (1 << m) - 1
    sol = []

    def odd_count(R):
        c = 0
        for v in range(n):
            d = 0
            for (w, j) in adj[v]:
                if R >> j & 1: d += 1
            c += d & 1
        return c

    @lru_cache(maxsize=None)
    def search(R, t):
        if R == 0: return True
        if t == 0: return False
        if bin(R).count('1') > t * (n - 1): return False
        if odd_count(R) > 2 * t: return False
        e = (R & -R).bit_length() - 1
        u, v = E[e]
        # enumerate paths containing e: left arm from u, right arm from v
        found = [False]
        def right(pe, vis, end, lefts):
            if search(R & ~pe, t - 1):
                if want_solution: sol.append(pe)
                return True
            for (w, j) in adj[end]:
                if (R >> j & 1) and not (pe >> j & 1) and not (vis >> w & 1):
                    if right(pe | (1 << j), vis | (1 << w), w, lefts): return True
            return False
        def left(pe, vis, end):
            if right(pe, vis, v, None): return True
            for (w, j) in adj[end]:
                if (R >> j & 1) and not (pe >> j & 1) and not (vis >> w & 1):
                    if left(pe | (1 << j), vis | (1 << w), w): return True
            return False
        return left(1 << e, (1 << u) | (1 << v), u)

    ok = search(full, k)
    if want_solution:
        return ok, [[E[j] for j in range(m) if pe >> j & 1] for pe in sol]
    return ok

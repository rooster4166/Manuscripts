import itertools, sys
import networkx as nx
sys.setrecursionlimit(10000)
def q_all(G):
    nodes = list(G); vi = {v: i for i, v in enumerate(nodes)}
    E = list(G.edges()); idx = {frozenset(e): i for i, e in enumerate(E)}
    m = len(E); adj = {v: list(G[v]) for v in nodes}
    paths = {}
    def dfs(s, vis, u, mask):
        for w in adj[u]:
            if w in vis: continue
            m2 = mask | (1 << idx[frozenset((u, w))])
            key = (m2, frozenset((s, w)))
            paths[key] = (vi[s], vi[w])
            vis.add(w); dfs(s, vis, w, m2); vis.remove(w)
    for s in nodes: dfs(s, {s}, s, 0)
    bylow = [[] for _ in range(m)]
    for (mk, _), (a, b) in paths.items():
        for i in range(m):
            if mk >> i & 1: bylow[i].append((mk, a, b))
    memo = {}
    def f(R, U):
        if R == 0: return 0
        key = (R, U)
        if key in memo: return memo[key]
        low = (R & -R).bit_length() - 1
        best = 99
        for mk, a, b in bylow[low]:
            if mk & ~R: continue
            R2 = R & ~mk
            if (U >> a) & 1:
                r = f(R2, U & ~(1 << a))
                if r < best: best = r
            if (U >> b) & 1:
                r = f(R2, U & ~(1 << b))
                if r < best: best = r
            if best == 0: break
            r = 1 + f(R2, U)
            if r < best: best = r
            if best == 0: break
        memo[key] = best
        return best
    full = (1 << m) - 1; n = len(nodes)
    out = {}
    for k in range(1, n + 1):
        for c in itertools.combinations(range(n), k):
            U = sum(1 << i for i in c)
            out[frozenset(nodes[i] for i in c)] = f(full, U)
    return out

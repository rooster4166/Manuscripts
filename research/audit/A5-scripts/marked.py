"""Exact marked path cost q(F,S): min over path partitions and injective
assignments (path -> one of its ends in S, distinct sites) of #unassigned paths."""
import itertools, functools
import networkx as nx

def all_paths(G):
    idx = {frozenset(e): i for i, e in enumerate(G.edges())}
    out = []
    adj = {v: list(G[v]) for v in G}
    def dfs(s, path, vis, mask):
        u = path[-1]
        for w in adj[u]:
            if w in vis: continue
            m2 = mask | (1 << idx[frozenset((u, w))])
            if repr(w) > repr(s) or (type(w)==type(s) and w > s):
                pass
            out.append((m2, s, w))
            vis.add(w); path.append(w)
            dfs(s, path, vis, m2)
            vis.remove(w); path.pop()
    for s in G: dfs(s, [s], {s}, 0)
    # dedupe reversals: keep each (mask, {s,w}) once
    seen = {}
    for m, a, b in out:
        seen[(m, frozenset((a, b)))] = (a, b)
    return idx, [(m, ab[0], ab[1]) for (m, _), ab in seen.items()]

def q_all(G, marksets=None):
    """return dict S(frozenset) -> q(F,S) for given marksets (default: all nonempty)."""
    idx, paths = all_paths(G)
    m = len(idx); full = (1 << m) - 1
    nodes = list(G)
    bylow = [[] for _ in range(m)]
    for P in paths:
        mk = P[0]
        bylow_i = (mk & -mk).bit_length() - 1
        # a path covers its lowest edge; index paths by every edge they contain is
        # unnecessary: we always cover the lowest remaining edge, which must be the
        # lowest edge of the chosen path only if all lower edges are already gone.
        for i in range(m):
            if mk >> i & 1: bylow[i].append(P)
    res = {}
    if marksets is None:
        marksets = [frozenset(c) for k in range(1, len(nodes)+1) for c in itertools.combinations(nodes, k)]
    for S in marksets:
        Sl = sorted(S, key=repr); pos = {v: i for i, v in enumerate(Sl)}
        @functools.lru_cache(maxsize=None)
        def f(R, U):
            if R == 0: return 0
            low = (R & -R).bit_length() - 1
            best = 99
            for mk, a, b in bylow[low]:
                if mk & ~R: continue
                r = f(R & ~mk, U)
                if 1 + r < best: best = 1 + r
                for x in (a, b):
                    if x in pos and (U >> pos[x]) & 1:
                        r2 = f(R & ~mk, U & ~(1 << pos[x]))
                        if r2 < best: best = r2
                if best == 0: break
            return best
        res[S] = f(full, (1 << len(Sl)) - 1)
        f.cache_clear()
    return res

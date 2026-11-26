"""Check: for every set of k edges of K_{2k+1} (k=2,3), there is a Hamilton
decomposition with the k edges on distinct cycles (Javadi-Miralaei form used in Thm 2)."""
import itertools, networkx as nx
from networkx.algorithms import isomorphism
def ham_cycles(n, allowed):
    """all Hamilton cycles (as frozenset of edges) within allowed edge set, through vertex 0"""
    adj = {v: [w for w in range(n) if frozenset((v, w)) in allowed] for v in range(n)}
    out = set()
    def dfs(path, vis):
        u = path[-1]
        if len(path) == n:
            if frozenset((u, 0)) in allowed:
                out.add(frozenset(frozenset((path[i], path[(i+1) % n])) for i in range(n)))
            return
        for w in adj[u]:
            if w not in vis:
                vis.add(w); path.append(w); dfs(path, vis); path.pop(); vis.remove(w)
    dfs([0], {0})
    return out
def rainbow(n, edges):
    k = len(edges)
    allE = frozenset(frozenset(e) for e in itertools.combinations(range(n), 2))
    def rec(i, remaining):
        if i == k: return not remaining
        for H in ham_cycles(n, remaining):
            if edges[i] in H and all(edges[j] not in H for j in range(k) if j != i):
                if rec(i + 1, remaining - H): return True
        return False
    return rec(0, allE)
for k in (1, 2, 3):
    n = 2 * k + 1
    allE = list(itertools.combinations(range(n), 2))
    reps = []
    for S in itertools.combinations(allE, k):
        H = nx.Graph(); H.add_edges_from(S)
        if not any(nx.is_isomorphic(H, R) for R in reps): reps.append(H)
    res = []
    for H in reps:
        edges = [frozenset(e) for e in H.edges()]
        res.append((sorted(tuple(sorted(e)) for e in edges), rainbow(n, edges)))
    print(f"K{n}, k={k}: {len(reps)} edge-set types; all rainbow-decomposable: {all(r for _, r in res)}", res)

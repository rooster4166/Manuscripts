import sys, time, networkx as nx
from circ import ham_decomp, check
def edge_graphs(m):
    """All graphs with m edges and no isolated vertices, up to isomorphism."""
    cur = [nx.Graph([(0, 1)])]
    for e in range(2, m + 1):
        nxt = []; buckets = {}
        for G in cur:
            V = list(G.nodes()); nv = len(V)
            cands = [(u, v) for i, u in enumerate(V) for v in V[i+1:] if not G.has_edge(u, v)]
            cands += [(u, nv) for u in V] + [(nv, nv + 1)]
            for (u, v) in cands:
                K = G.copy(); K.add_edge(u, v)
                key = nx.weisfeiler_lehman_graph_hash(K, iterations=3)
                lst = buckets.setdefault(key, [])
                if any(nx.is_isomorphic(K, L) for L in lst): continue
                lst.append(K); nxt.append(K)
        cur = nxt
    return cur

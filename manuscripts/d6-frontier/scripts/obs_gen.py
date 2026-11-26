import sys, random, itertools
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from pathnum2 import decompose
from pathnum import verify_partition

def gen(m, nfull, rng, p_ext=0.5, p_con=0.6):
    """K6 core on 0..5, exterior 6..6+m-1, first nfull exterior vertices full."""
    U = list(range(6)); X = list(range(6, 6 + m))
    while True:
        G = nx.complete_graph(6)
        G.add_nodes_from(X)
        for i, x in enumerate(X):
            for u in U:
                if i < nfull or rng.random() < p_con:
                    G.add_edge(x, u)
        for a, b in itertools.combinations(X, 2):
            if rng.random() < p_ext:
                G.add_edge(a, b)
        # fix U parity using non-full exterior vertices
        nonfull = X[nfull:]
        ok = True
        for u in U:
            if G.degree(u) % 2:
                cands = nonfull[:]
                rng.shuffle(cands)
                if not cands: ok = False; break
                x = cands[0]
                if G.has_edge(u, x): G.remove_edge(u, x)
                else: G.add_edge(u, x)
        if not ok: continue
        bad = [x for x in X if G.degree(x) % 2 == 0]
        rng.shuffle(bad)
        for a, b in zip(bad[::2], bad[1::2]):
            if G.has_edge(a, b): G.remove_edge(a, b)
            else: G.add_edge(a, b)
        if any(G.degree(u) % 2 for u in U): continue
        if any(G.degree(x) % 2 == 0 for x in X): continue
        if not nx.is_connected(G): continue
        if not all(set(U) <= set(G[X[i]]) for i in range(nfull)): continue
        return G

def realisable(G, S, U, k, tl=60):
    ex = {v: 1 for v in G if G.degree(v) % 2}
    for u in U: ex[u] = 2 if u in S else 0
    st, P = decompose(G, k, exact_ends=ex, time_limit=tl, workers=2)
    if P is not None: assert verify_partition(G, P)
    return st, P

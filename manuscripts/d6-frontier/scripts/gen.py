"""Random graphs with d even vertices U = {0..d-1} (default d = 6) inducing K_d, with prescribed local
gadgets (required and forbidden edges), all other vertices odd.  Parity is repaired by
toggling allowed edges between wrong-parity vertices."""
import itertools, random
import networkx as nx

def build(n, required, forbidden, rng, p=0.45, tries=2000, d=6):
    U = list(range(d))
    V = list(range(n))
    req = set(map(frozenset, required)) | {frozenset(e) for e in itertools.combinations(U, 2)}
    forb = set(map(frozenset, forbidden))
    allowed = [frozenset(e) for e in itertools.combinations(V, 2)
               if frozenset(e) not in req and frozenset(e) not in forb]
    for _ in range(tries):
        G = nx.Graph(); G.add_nodes_from(V)
        G.add_edges_from(tuple(e) for e in req)
        for e in allowed:
            if rng.random() < p:
                G.add_edge(*tuple(e))
        def wrong():
            return [v for v in V if (G.degree(v) % 2 == 0) != (v in U)]
        for _ in range(200):
            W = wrong()
            if not W: break
            rng.shuffle(W)
            done = False
            for a, b in itertools.combinations(W, 2):
                e = frozenset((a, b))
                if e in req or e in forb: continue
                if G.has_edge(a, b): G.remove_edge(a, b)
                else: G.add_edge(a, b)
                done = True; break
            if not done:
                a = W[0]
                cands = [e for e in allowed if a in e]
                e = rng.choice(cands)
                x, y = tuple(e)
                if G.has_edge(x, y): G.remove_edge(x, y)
                else: G.add_edge(x, y)
        if wrong(): continue
        if not nx.is_connected(G): continue
        if any(G.degree(v) == 0 for v in V): continue
        return G
    return None

import itertools, random
import networkx as nx
U = list(range(6))
# rooted shapes with r = 0 at an allowed position: D edges on U
ROOTED = {
    'empty': [],
    'K2_on': [(0, 1)], 'K2_off': [(1, 2)],
    'P3_mid': [(1, 0), (0, 2)],
    'K3': [(0, 1), (1, 2), (0, 2)],
    'C4': [(0, 1), (1, 2), (2, 3), (3, 0)],
}
def core_from_D(D):
    G = nx.complete_graph(6)
    G.remove_edges_from(D)
    return G
def random_host(rng, D, nX, pXX=None, pXU=None, maxS=6, tries=200):
    for _ in range(tries):
        G = core_from_D(D)
        X = list(range(6, 6 + nX))
        G.add_nodes_from(X)
        pXX = rng.uniform(0.1, 0.9) if pXX is None else pXX
        pXU = rng.uniform(0.1, 0.9) if pXU is None else pXU
        for a, b in itertools.combinations(X, 2):
            if rng.random() < pXX: G.add_edge(a, b)
        for x in X:
            for u in U:
                if rng.random() < pXU: G.add_edge(x, u)
        wrong = [v for v in G if (G.degree(v) % 2) != (0 if v < 6 else 1)]
        rng.shuffle(wrong)
        if len(wrong) % 2: continue
        for p, q in zip(wrong[::2], wrong[1::2]):
            if p < 6 and q < 6:
                x = rng.choice(X)
                for y in (p, q):
                    if G.has_edge(x, y): G.remove_edge(x, y)
                    else: G.add_edge(x, y)
            else:
                if G.has_edge(p, q): G.remove_edge(p, q)
                else: G.add_edge(p, q)
        if not all((G.degree(v) % 2) == (0 if v < 6 else 1) for v in G): continue
        if any(G.degree(v) == 0 for v in G) or not nx.is_connected(G): continue
        if any(len([u for u in U if G.has_edge(x, u)]) > maxS for x in X): continue
        # core must be unchanged
        if set(map(frozenset, core_from_D(D).edges())) != set(frozenset(e) for e in G.subgraph(U).edges()): continue
        return G
    return None

"""Self-test of fan_engine: on random graphs and random path decompositions, whenever
Fan's grouped inequality sum_T b > #blank neighbours of u holds, fan_add must succeed and
its output must be a valid decomposition of H + tu with the predicted end vector."""
import random, sys
import networkx as nx
from fan_engine import fan_add, ends, verify, blank_nbrs, nbrs

def random_decomp(G, rng):
    E = list(G.edges()); rng.shuffle(E)
    H = nx.Graph(); H.add_nodes_from(G); D = []
    left = set(map(frozenset, E))
    while left:
        e = next(iter(left)); a, b = tuple(e); P = [a, b]; left.discard(e)
        grow = True
        while grow:
            grow = False
            for end in (0, 1):
                v = P[-1] if end else P[0]
                cand = [w for w in G[v] if frozenset((v, w)) in left and w not in P]
                if cand and rng.random() < 0.8:
                    w = rng.choice(cand); left.discard(frozenset((v, w)))
                    if end: P.append(w)
                    else: P.insert(0, w)
                    grow = True
        D.append(tuple(P))
    return D

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
tests = 0
while tests < 400:
    n = rng.randint(5, 10)
    G = nx.gnp_random_graph(n, rng.uniform(0.3, 0.8), seed=rng.randrange(10**9))
    if G.number_of_edges() < 3: continue
    D = random_decomp(G, rng)
    b = ends(D, G.nodes())
    u = rng.choice(list(G))
    non = [w for w in G if w != u and not G.has_edge(w, u)]
    if not non: continue
    T = rng.sample(non, rng.randint(1, min(4, len(non))))
    if sum(b[t] for t in T) <= blank_nbrs(D, G.nodes(), u): continue
    res = fan_add(D, u, T)
    assert res is not None, "Fan inequality held but no chain found"
    D2, t = res
    G2 = G.copy(); G2.add_edge(t, u)
    assert verify(D2, G2) and len(D2) == len(D)
    b2 = ends(D2, G2.nodes())
    want = dict(b); want[t] -= 1; want[u] += 1
    assert b2 == want
    tests += 1
print("fan_engine self-test passed on", tests, "instances")

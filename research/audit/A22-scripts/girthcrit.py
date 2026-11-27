"""girthcrit.py: random test of the criterion after Corollary 7.2: J* = (J-z)+ab+cd has girth >= 5 iff
J-z has girth >= 5, d(a,b), d(c,d) >= 4, d(a,c)+d(b,d) >= 3 and d(a,d)+d(b,c) >= 3 (distances in J-z)."""
import random, itertools
import networkx as nx
rnd = random.Random(5); INF = 10 ** 9
def girth_ge5(H):
    for u, v in H.edges():
        K = H.copy(); K.remove_edge(u, v)
        try:
            if nx.shortest_path_length(K, u, v) <= 3: return False
        except nx.NetworkXNoPath: pass
    return True
def d(H, u, v):
    try: return nx.shortest_path_length(H, u, v)
    except nx.NetworkXNoPath: return INF
tests = mism = 0
for _ in range(4000):
    n = rnd.randint(6, 12)
    H = nx.gnp_random_graph(n, rnd.uniform(0.08, 0.35), seed=rnd.randrange(10 ** 9))
    a, b, c, dd = rnd.sample(range(n), 4)
    if H.has_edge(a, b) or H.has_edge(c, dd): continue
    Js = H.copy(); Js.add_edges_from([(a, b), (c, dd)])
    lhs = girth_ge5(Js)
    rhs = girth_ge5(H) and d(H, a, b) >= 4 and d(H, c, dd) >= 4 and d(H, a, c) + d(H, b, dd) >= 3 and d(H, a, dd) + d(H, b, c) >= 3
    tests += 1; mism += lhs != rhs
print('tests', tests, 'mismatches', mism)

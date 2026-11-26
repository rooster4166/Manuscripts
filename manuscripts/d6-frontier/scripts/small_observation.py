"""Small observation (Section 8 of d6-frontier.tex): realisability of every 3-subset of U
(b = 2 on the triple, 0 on the rest of U, 1 on odd vertices, k paths) in
 (1) the false-twin example K10 minus the six edges from 9 to U = {0..5};
 (2) nine random graphs with B[U] = K6 and one or two full exterior vertices
     (generator obs_gen.gen with the seeds below; orders 10 and 12).
Evidence only; not used in any proof."""
import sys, random, itertools
sys.path.insert(0, '/home/user/Manuscripts/tools')
sys.path.insert(0, __import__('os').path.dirname(__file__))
import networkx as nx
from obs_gen import gen, realisable

U = list(range(6))
def all_triples(G):
    k = G.number_of_nodes() // 2
    bad = []
    for S in itertools.combinations(U, 3):
        st, P = realisable(G, S, U, k)
        if P is None: bad.append((S, st))
    return bad

G = nx.complete_graph(10)
for u in U: G.remove_edge(9, u)
print("false-twin example: non-realisable triples:", all_triples(G), flush=True)
for seed, m, nf, cnt in ((1, 4, 1, 4), (2, 6, 1, 3), (3, 6, 2, 2)):
    rng = random.Random(seed)
    for _ in range(cnt):
        H = gen(m, nf, rng)
        print("n", H.number_of_nodes(), "full", nf, "degrees", [H.degree(v) for v in H],
              "non-realisable triples:", all_triples(H), flush=True)

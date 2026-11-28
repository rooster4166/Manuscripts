"""randg.py: random connected graphs with exactly one vertex of positive even degree (odd n), as
graph6 on stdout.  G(n,p), p uniform in [PLO, PHI], parities repaired by toggling edges between
pairs of even vertices (as in l1star/scripts/rand_max.py).
usage: python3 randg.py N_GRAPHS SEED n1 [n2 ...]"""
import sys, random, os
import networkx as nx
PLO, PHI = float(os.environ.get("PLO", "0.2")), float(os.environ.get("PHI", "0.6"))
def random_graph(n, p, rng):
    for _ in range(1000):
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(1 << 30))
        if not nx.is_connected(G): continue
        ev = [v for v in G if G.degree(v) % 2 == 0]
        if len(ev) % 2:
            g = rng.choice(ev); ev = [v for v in ev if v != g]
        rng.shuffle(ev)
        for i in range(0, len(ev), 2):
            a, b = ev[i], ev[i + 1]
            if G.has_edge(a, b): G.remove_edge(a, b)
            else: G.add_edge(a, b)
        if not nx.is_connected(G) or G.number_of_edges() > 120: continue
        if len([v for v in G if G.degree(v) % 2 == 0]) != 1: continue
        return G
    return None
N, seed = int(sys.argv[1]), int(sys.argv[2]); ns = [int(x) for x in sys.argv[3:]]
rng = random.Random(seed)
for i in range(N):
    n = ns[i % len(ns)]
    G = random_graph(n, rng.uniform(PLO, PHI), rng)
    if G is not None: print(nx.to_graph6_bytes(G, header=False).decode().strip())

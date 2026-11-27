"""random_euler.py N COUNT SEED [P ...]: random 2-connected Eulerian graphs (graph6 on stdout).

For each edge probability P (default 0.2 .. 0.8), draw G(N, P), then repeatedly take two odd
vertices u, v and toggle the pair uv (add the edge if absent, delete it if present), which makes
both even.  Keep the result if it is 2-connected.  The distribution is not uniform; this is a
sampler for testing only.
"""
import random
import sys

import networkx as nx

N, COUNT, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
PS = [float(x) for x in sys.argv[4:]] or [0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8]
rng = random.Random(SEED)
for p in PS:
    got = 0
    while got < COUNT:
        G = nx.gnp_random_graph(N, p, seed=rng.randrange(1 << 30))
        odd = [v for v in G if G.degree(v) % 2]
        rng.shuffle(odd)
        for i in range(0, len(odd), 2):
            u, v = odd[i], odd[i + 1]
            if G.has_edge(u, v):
                G.remove_edge(u, v)
            else:
                G.add_edge(u, v)
        assert all(d % 2 == 0 for _, d in G.degree())
        if nx.is_biconnected(G) and G.number_of_nodes() == N:
            print(nx.to_graph6_bytes(G, header=False).decode().strip())
            got += 1

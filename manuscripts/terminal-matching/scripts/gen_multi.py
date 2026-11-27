"""Random graphs G' for ptm mode p (multigraph case): connected, 2-connected if required,
with exactly 2M vertices of even degree (degree-0 vertices excluded).  ptm p M then tests every
perfect matching F of Ev(G') (pairs may be adjacent in G', i.e. parallel F-edges).
usage: gen_multi.py n M count seed [2conn]"""
import sys, random
import networkx as nx
n, M, count, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
two = len(sys.argv) > 5 and sys.argv[5] == '2conn'
rng = random.Random(seed); made = 0
while made < count:
    G = nx.gnp_random_graph(n, rng.uniform(0.2, 0.5), seed=rng.randrange(1 << 30))
    ev = [v for v in G if G.degree(v) % 2 == 0]
    rng.shuffle(ev)
    # toggle pairs of even vertices until exactly 2M remain
    while len(ev) > 2 * M:
        u, v = ev.pop(), ev.pop()
        if G.has_edge(u, v): G.remove_edge(u, v)
        else: G.add_edge(u, v)
    if len(ev) != 2 * M or any(G.degree(v) == 0 for v in G): continue
    if not nx.is_connected(G): continue
    if two and not nx.is_biconnected(G): continue
    print(nx.to_graph6_bytes(G, header=False).decode().strip()); made += 1

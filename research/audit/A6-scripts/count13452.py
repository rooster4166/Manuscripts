import itertools, networkx as nx
tot = 0; per = {}
for n in range(1, 7):
    pairs = list(itertools.combinations(range(n), 2)); c = 0
    for s in range(1 << len(pairs)):
        G = nx.Graph(); G.add_nodes_from(range(n))
        G.add_edges_from(pairs[i] for i in range(len(pairs)) if s >> i & 1)
        if G.degree(0) > 0 and G.degree(0) % 2 == 0 and nx.is_connected(G): c += 1
    per[n] = c; tot += c
print(per, tot)

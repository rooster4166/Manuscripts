"""multipartite.py: graph6 of every complete multipartite graph with all parts of even size and
order 4 <= n <= 16 (these are exactly the Eulerian complete multipartite graphs of even order)."""
import networkx as nx


def parts(n, mx):
    if n == 0:
        yield []
        return
    for a in range(min(n, mx), 1, -1):
        if a % 2 == 0:
            for rest in parts(n - a, a):
                yield [a] + rest


for n in range(4, 17, 2):
    for P in parts(n, n):
        if len(P) < 2:
            continue
        G = nx.convert_node_labels_to_integers(nx.complete_multipartite_graph(*P))
        assert nx.is_biconnected(G) and all(d % 2 == 0 for _, d in G.degree())
        print(nx.to_graph6_bytes(G, header=False).decode().strip())

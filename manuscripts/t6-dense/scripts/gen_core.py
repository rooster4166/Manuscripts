"""Random J with a prescribed dense core at z (the T(6)-i residual shapes).

J: z of degree 6 with N(z) = U = {1..6}; B = J - z has B[U] = K6 - D for D one of
  empty, K2, P3, K3, C4 (on the vertices 1..4 of U);
every vertex of U has an odd number (1 or 3) of exterior neighbours, so that it has even degree in
B and odd degree in J; exterior vertices have degree 3 or 5; J 3-connected, z its only even vertex.
Prints g6(B) lines (B = J - z relabelled 0..n-2, U = 0..5), one per graph.

usage: gen_core.py D COUNT N_EXT SEED     (D in: empty K2 P3 K3 C4)
"""
import sys, random
import networkx as nx

DS = {'empty': [], 'K2': [(1, 2)], 'P3': [(1, 2), (2, 3)], 'K3': [(1, 2), (2, 3), (1, 3)],
      'C4': [(1, 2), (2, 3), (3, 4), (4, 1)]}


def build(rng, D, next_):
    G = nx.Graph()
    U = list(range(1, 7))
    G.add_nodes_from(range(7 + next_))
    for u in U:
        G.add_edge(0, u)
    for i in U:
        for j in U:
            if i < j and (i, j) not in D and (j, i) not in D:
                G.add_edge(i, j)
    ext = list(range(7, 7 + next_))
    ustubs = []
    for u in U:
        ustubs += [u] * rng.choice((1, 1, 3))
    estubs = []
    for x in ext:
        estubs += [x] * rng.choice((3, 3, 3, 5))
    rng.shuffle(estubs)
    if len(ustubs) > len(estubs):
        return None
    for u in ustubs:
        x = estubs.pop()
        if G.has_edge(u, x):
            return None
        G.add_edge(u, x)
    if len(estubs) % 2:
        return None
    for a, b in zip(estubs[::2], estubs[1::2]):
        if a == b or G.has_edge(a, b):
            return None
        G.add_edge(a, b)
    if any(G.degree(v) % 2 == 0 for v in G if v != 0) or G.degree(0) != 6:
        return None
    if nx.node_connectivity(G) < 3:
        return None
    return G


def main():
    D = DS[sys.argv[1]]
    count, next_, seed = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(seed)
    made = tries = 0
    while made < count and tries < 20000 * count:
        tries += 1
        G = build(rng, D, next_)
        if G is None:
            continue
        made += 1
        H = G.copy()
        H.remove_node(0)
        H = nx.convert_node_labels_to_integers(H, ordering='sorted')
        print(nx.to_graph6_bytes(H, header=False).decode().strip(), flush=True)
    print(f'# made={made} tries={tries}', file=sys.stderr)


if __name__ == '__main__':
    main()

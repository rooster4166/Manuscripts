"""gen_t2.py: random 3-connected graphs J of order n whose only even vertices are an adjacent pair.

For each density p: draw G(n, p); choose z, r; repair parities by toggling the edges of a pairing
of the vertices with the wrong parity (target: z, r even, the rest odd); add zr if missing and
repair again; keep J if it is 3-connected with exactly two even vertices, adjacent.  Prints graph6
(one line per graph, duplicates up to isomorphism not removed).
usage: python3 gen_t2.py n count seed [pmin pmax]
"""
import random
import sys

import networkx as nx


def repair(G, z, r, rng):
    for _ in range(4):
        wrong = [v for v in G if (G.degree(v) % 2 == 0) != (v in (z, r))]
        rng.shuffle(wrong)
        for a, b in zip(wrong[::2], wrong[1::2]):
            if G.has_edge(a, b):
                G.remove_edge(a, b)
            else:
                G.add_edge(a, b)
        if not G.has_edge(z, r):
            G.add_edge(z, r)
            # z and r both flipped; flip them back through a common non-neighbour pair
            continue
        if all((G.degree(v) % 2 == 0) == (v in (z, r)) for v in G):
            return True
    return False


def main():
    n, count, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    pmin = float(sys.argv[4]) if len(sys.argv) > 4 else 0.3
    pmax = float(sys.argv[5]) if len(sys.argv) > 5 else 0.9
    rng = random.Random(seed)
    out = 0
    while out < count:
        p = rng.uniform(pmin, pmax)
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(10 ** 9))
        z, r = rng.sample(range(n), 2)
        if not repair(G, z, r, rng):
            continue
        ev = [v for v in G if G.degree(v) % 2 == 0]
        if sorted(ev) != sorted((z, r)) or not G.has_edge(z, r):
            continue
        if nx.node_connectivity(G) < 3:
            continue
        print(nx.to_graph6_bytes(G, header=False).decode().strip())
        out += 1


if __name__ == "__main__":
    main()

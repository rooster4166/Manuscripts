"""Random test of: m edge-disjoint cycles through x  =>  F_2(union, x) <= m + 1.

F_2(G, x) = min number of paths in a decomposition with >= 2 ends at x.
(marked-reduction Thm 175 proves m = 8; cycle-and-contact Thm 1 proves m = 12 in
the nearly spanning case; Cor 176 gives m + floor(sqrt m) - 1 in general.)
"""
import random
import sys
import networkx as nx
from pathnum import solve


def random_cycle_family(m, N, rng, max_tries=2000):
    G = nx.Graph()
    G.add_node(0)
    cycles = []
    tries = 0
    while len(cycles) < m and tries < max_tries:
        tries += 1
        L = rng.randint(3, N)
        others = rng.sample(range(1, N), L - 1)
        cyc = [0] + others
        es = [(cyc[i], cyc[(i + 1) % L]) for i in range(L)]
        if any(G.has_edge(a, b) for a, b in es):
            continue
        G.add_edges_from(es)
        cycles.append(cyc)
    return G if len(cycles) == m else None


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    worst = {}
    for t in range(trials):
        m = rng.randint(2, 6)
        N = rng.randint(2 * m + 1, 2 * m + 5)
        G = random_cycle_family(m, N, rng)
        if G is None or G.number_of_edges() > 30:
            continue
        r = solve(G, min_ends={0: 2}, time_limit=60)
        val = r.value
        if val is None:
            print("timeout", m, N); continue
        key = m
        worst[key] = max(worst.get(key, 0), val - m)
        if val > m + 1:
            print("COUNTEREXAMPLE", m, N, sorted(G.edges()), val)
    print("max (F2 - m) by m:", dict(sorted(worst.items())))

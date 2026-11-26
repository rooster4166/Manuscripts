"""Random test of the Endpoint Matroid Conjecture on critical graphs.

Samples connected sparse graphs of even order n, keeps the critical ones
(p = n/2) having at least 4 even vertices, and checks that the minimal
realisable sets are the bases of a loopless matroid of rank e/2.
"""
import random
import sys
import networkx as nx
from pathnum import path_number, lower_bound
from realisable_matroid import analyse


def sample(n, m, rng):
    while True:
        G = nx.gnm_random_graph(n, m, seed=rng.randrange(1 << 30))
        if nx.is_connected(G):
            return G


if __name__ == "__main__":
    n = int(sys.argv[1]); trials = int(sys.argv[2]); seed = int(sys.argv[3])
    rng = random.Random(seed)
    crit = ok = 0
    for t in range(trials):
        m = rng.randint(n, int(1.9 * n))
        G = sample(n, m, rng)
        e = sum(1 for v in G if G.degree(v) % 2 == 0)
        if e < 4:
            continue
        if path_number(G, time_limit=30) != n // 2:
            continue
        crit += 1
        e_, sizes, is_matroid, loops = analyse(G)
        good = is_matroid and not loops and sizes == [e // 2]
        ok += good
        if not good:
            print("EMC-FAIL", nx.to_graph6_bytes(G, header=False).decode().strip(), "e=", e, sizes, is_matroid, loops, flush=True)
    print(f"n={n}: critical graphs tested {crit}, EMC holds {ok}", flush=True)

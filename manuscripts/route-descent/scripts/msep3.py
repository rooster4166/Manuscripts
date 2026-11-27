"""Multi-pair separation at distance >= 3 (multi-SEP3), targeted test.

F: random graph with all degrees odd.  N: a random perfect (or near-perfect) matching of pairs at
F-distance >= 3.  Question: does F have a Lovasz decomposition (one end per vertex) in which no path
contains both vertices of a pair?  (Oracle query S.)  multi-SEP3 would give: every graph G whose
even subgraph has a perfect matching N with no edge of N in a triangle of G satisfies Gallai, with
every orientation of N realisable.

Usage: python3 msep3.py trials budget [seed]
"""
import random
import sys

import networkx as nx

import rd_lib as L
from lovasz_matching import make_all_odd


def far_matching(F, rng, tries=200):
    d = dict(nx.all_pairs_shortest_path_length(F))
    V = list(F)
    best = []
    for _ in range(tries):
        rng.shuffle(V)
        used, N = set(), []
        for u in V:
            if u in used:
                continue
            cand = [w for w in V if w not in used and w != u and d[u].get(w, 99) >= 3]
            if cand:
                w = rng.choice(cand)
                N.append((u, w))
                used |= {u, w}
        if len(N) > len(best):
            best = N
        if 2 * len(best) == len(V):
            break
    return best


def main():
    trials = int(sys.argv[1])
    L.BUDGET = int(sys.argv[2])
    L.FINAL = False
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 5)
    st = {}
    for it in range(trials):
        n = rng.choice([8, 10, 12, 14, 16])
        F = nx.gnp_random_graph(n, rng.uniform(0.12, 0.45), seed=rng.randrange(10 ** 9))
        if not make_all_odd(F, rng) or F.number_of_edges() > 120:
            continue
        N = far_matching(F, rng)
        if not N:
            continue
        perfect = 2 * len(N) == n
        r = L.sep(F, [1] * n, N)
        k = (n, perfect)
        st.setdefault(k, [0, 0, 0])
        st[k][0] += 1
        if r is None:
            st[k][2] += 1
        elif not r:
            st[k][1] += 1
            print("FAIL", sorted(F.edges()), N, flush=True)
    print("(n, perfect) -> failures/total (undecided):",
          {k: f"{v[1]}/{v[0]} ({v[2]})" for k, v in sorted(st.items())})


if __name__ == "__main__":
    main()

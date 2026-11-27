"""Separation (no path contains both c and a) for all-odd graphs at distance exactly 2, and with one
even vertex.  Usage: python3 sep2.py trials budget"""
import random
import sys

import networkx as nx

import rd_lib as L
from lovasz_matching import make_all_odd
from l1_search import fix_parity_except


def main():
    trials, L.BUDGET, L.FINAL = int(sys.argv[1]), int(sys.argv[2]), False
    rng = random.Random(41)
    st = {}
    ex = {}
    for it in range(trials):
        mode = rng.choice(["odd", "even"])
        n = rng.choice([6, 8, 10, 12]) if mode == "odd" else rng.choice([5, 7, 9, 11])
        F = nx.gnp_random_graph(n, rng.uniform(0.15, 0.7), seed=rng.randrange(10 ** 9))
        if mode == "odd":
            if not make_all_odd(F, rng):
                continue
            b = [1] * n
        else:
            if not fix_parity_except(F, rng, 0) or F.degree(0) == 0:
                continue
            b = [0] + [1] * (n - 1)
        d = dict(nx.all_pairs_shortest_path_length(F))
        prs = [(c, a) for c in F for a in F if c < a and d[c].get(a) == 2]
        for c, a in rng.sample(prs, min(4, len(prs))):
            r = L.sep(F, b, c, a)
            k = mode
            st.setdefault(k, [0, 0, 0])
            st[k][0] += 1
            if r is None:
                st[k][2] += 1
            elif not r:
                st[k][1] += 1
                if k not in ex:
                    ex[k] = (sorted(F.edges()), c, a)
    print("distance-2 separation, failures/total (undecided):", {k: f"{v[1]}/{v[0]} ({v[2]})" for k, v in st.items()})
    for k, v in ex.items():
        print(k, v)


if __name__ == "__main__":
    main()

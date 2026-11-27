"""Q_s within N[s] in graphs with one positive-even vertex z, split by whether z ~ s.
Usage: python3 lloc_z_test.py trials budget nmin nmax"""
import random
import sys

import networkx as nx

import rd_lib as L
from l1_search import fix_parity_except


def main():
    trials, L.BUDGET, L.FINAL = int(sys.argv[1]), int(sys.argv[2]), False
    nmin, nmax = int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(8080)
    st = {"z~s": [0, 0, 0], "z!~s": [0, 0, 0]}
    for it in range(trials):
        n = rng.choice([x for x in range(nmin, nmax + 1) if x % 2])
        F = nx.gnp_random_graph(n, rng.uniform(0.15, 0.6), seed=rng.randrange(10 ** 9))
        if not fix_parity_except(F, rng, 0) or F.degree(0) == 0 or F.number_of_edges() > 100:
            continue
        b = [0 if v == 0 else 1 for v in range(n)]
        cand = [v for v in F if v != 0 and F.degree(v) % 2 == 1]
        for s in rng.sample(cand, min(3, len(cand))):
            Y = {v for v in F if v != s and not F.has_edge(s, v)}
            if not Y:
                continue
            key = "z~s" if F.has_edge(0, s) else "z!~s"
            r = L.avoid(F, b, {s: Y})
            st[key][0] += 1
            if r is None:
                st[key][2] += 1
            elif not r:
                st[key][1] += 1
                if st[key][1] <= 3:
                    print("FAIL", key, n, sorted(F.edges()), "s", s, flush=True)
    print("Q_s in N[s], one even vertex z: [total, failures, undecided]", st)


if __name__ == "__main__":
    main()

"""Classify L1 failures with one positive even vertex z by the position of z.
Usage: python3 l1z_classify.py trials budget nmin nmax"""
import random
import sys
from collections import Counter

import networkx as nx

import rd_lib as L
from l1_search import fix_parity_except


def main():
    trials, L.BUDGET, L.FINAL = int(sys.argv[1]), int(sys.argv[2]), False
    nmin, nmax = int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(99)
    tot, fail = Counter(), Counter()
    ex = {}
    for it in range(trials):
        n = rng.choice([x for x in range(nmin, nmax + 1) if x % 2])
        F = nx.gnp_random_graph(n, rng.uniform(0.2, 0.7), seed=rng.randrange(10 ** 9))
        z = 0
        if not fix_parity_except(F, rng, z) or F.degree(z) == 0 or F.number_of_edges() > 120:
            continue
        b = [0 if v == z else 1 for v in range(n)]
        odd = [v for v in F if v != z and F.degree(v) > 0]
        pairs = [(c, a) for c in odd for a in odd if c != a and not F.has_edge(c, a)]
        for c, a in rng.sample(pairs, min(4, len(pairs))):
            d = nx.shortest_path_length(F, c, a) if nx.has_path(F, c, a) else 99
            Nz = set(F[z])
            key = (min(d, 4), z in F[c], z in F[a], Nz <= set(F[c]) | {c, a},
                   Nz <= set(F[a]) | {c, a} | set(F[c]))
            r = L.avoid(F, b, {c: {a}})
            if r is None:
                continue
            tot[key] += 1
            if not r:
                fail[key] += 1
                ex.setdefault(key, (n, sorted(F.edges()), c, a))
    print("key = (dist(c,a) capped 4, z~c, z~a, N(z) in N[c]+a, N(z) in N[c]+N[a]) : fail/total")
    for k in sorted(tot):
        print(k, f"{fail[k]}/{tot[k]}")
    for k, e in ex.items():
        print("EX", k, e)


if __name__ == "__main__":
    main()

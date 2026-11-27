"""L1 and the symmetric-ends variant S1 with one positive even vertex z (the inductive setting of
Lovasz's strong form).

K: random graph, exactly one positive-even vertex z (or none), c, a odd, non-adjacent, at distance 2
(common neighbour).  Tests
  L1 : some Lovasz decomposition has Q_c avoiding a;
  S1 : some Lovasz decomposition has Q_c avoiding a and Q_a avoiding c.
Usage: python3 l1z_test.py trials budget [nmin nmax] [mode]   mode: z (one even vertex) | odd
"""
import random
import sys

import networkx as nx

import rd_lib as L
from l1_search import fix_parity_except
from lovasz_matching import make_all_odd


def main():
    trials, L.BUDGET, L.FINAL = int(sys.argv[1]), int(sys.argv[2]), False
    nmin = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    nmax = int(sys.argv[4]) if len(sys.argv) > 4 else 11
    mode = sys.argv[5] if len(sys.argv) > 5 else "z"
    rng = random.Random(4242)
    st = {"L1": [0, 0, 0], "S1": [0, 0, 0]}
    for it in range(trials):
        n = rng.randint(nmin, nmax)
        F = nx.gnp_random_graph(n, rng.uniform(0.2, 0.7), seed=rng.randrange(10 ** 9))
        if mode == "z":
            if n % 2 == 0:
                continue
            z = 0
            if not fix_parity_except(F, rng, z) or F.degree(z) == 0:
                continue
            b = [0 if v == z else 1 for v in range(n)]
            odd = [v for v in F if v != z and F.degree(v) > 0]
        else:
            if n % 2 or not make_all_odd(F, rng):
                continue
            b = [1] * n
            odd = list(F)
        if F.number_of_edges() > 120:
            continue
        pairs = [(c, a) for c in odd for a in odd if c != a and not F.has_edge(c, a)
                 and set(F[c]) & set(F[a])]
        if not pairs:
            continue
        for c, a in rng.sample(pairs, min(3, len(pairs))):
            for key, X in (("L1", {c: {a}}), ("S1", {c: {a}, a: {c}})):
                r = L.avoid(F, b, X)
                s = st[key]
                s[0] += 1
                if r is None:
                    s[2] += 1
                elif not r:
                    s[1] += 1
                    print("FAIL", key, n, sorted(F.edges()), "c", c, "a", a, "b", b, flush=True)
    print(mode, "key -> [total, failures, undecided]:", st)


if __name__ == "__main__":
    main()

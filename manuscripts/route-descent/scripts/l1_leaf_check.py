"""Check the leaf reduction of L1 to the separation theorem on random instances:
F all odd, c, a non-adjacent (distance 2 preferred).  K = F + l c.  Ask the oracle for a
separating (l, a) Lovasz decomposition of K (query S with witness via checker), strip l, and verify
it is a Lovasz decomposition of F whose path at c avoids a.
Usage: python3 l1_leaf_check.py trials budget"""
import random
import sys

import networkx as nx

import rd_lib as L
from lovasz_matching import make_all_odd


def main():
    trials, L.BUDGET, L.FINAL = int(sys.argv[1]), int(sys.argv[2]), False
    rng = random.Random(2027)
    ok = und = fail = 0
    for it in range(trials):
        n = rng.choice([6, 8, 10, 12])
        F = nx.gnp_random_graph(n, rng.uniform(0.2, 0.7), seed=rng.randrange(10 ** 9))
        if not make_all_odd(F, rng) or F.number_of_edges() > 100:
            continue
        pairs = [(c, a) for c in F for a in F if c != a and not F.has_edge(c, a)
                 and set(F[c]) & set(F[a])]
        if not pairs:
            continue
        c, a = rng.choice(pairs)
        K = nx.Graph(F)
        K.add_edge(c, n)
        b = [K.degree(v) % 2 for v in range(n + 1)]
        r = L.sep(K, b, n, a)
        if r is None:
            und += 1
        elif r:
            ok += 1
        else:
            fail += 1
            print("SEP FAIL (contradicts theorem)", sorted(F.edges()), c, a, flush=True)
    print(f"separating decompositions of F + lc: found {ok}, undecided {und}, none {fail}")


if __name__ == "__main__":
    main()

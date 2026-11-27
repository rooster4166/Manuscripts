"""Multi-leaf separation (MLS), candidate generalisation of the separation theorem.
F all odd; C a set of pairwise non-adjacent vertices; K = F + a leaf l_c at each c in C (so the
vertices of C are the even vertices of K); X = leaves + Y, packed in K (Y packed in F, Y outside
N[C]).  Is there a Lovasz decomposition of K in which every path meets X at most once?
Usage: python3 mls_test.py trials budget k ny [dmin]   (k = |C|, ny = |Y|, C pairwise at distance >= dmin)"""
import random
import sys
from itertools import combinations

import networkx as nx

import rd_lib as L
from lovasz_matching import make_all_odd


def main():
    trials, L.BUDGET, L.FINAL = int(sys.argv[1]), int(sys.argv[2]), False
    k, ny = int(sys.argv[3]), int(sys.argv[4])
    dmin = int(sys.argv[5]) if len(sys.argv) > 5 else 2
    rng = random.Random(555 + 10 * k + ny)
    tot = bad = und = 0
    for it in range(trials):
        n = rng.choice([8, 10, 12])
        F = nx.gnp_random_graph(n, rng.uniform(0.2, 0.6), seed=rng.randrange(10 ** 9))
        if not make_all_odd(F, rng) or F.number_of_edges() > 90:
            continue
        V = list(F)
        rng.shuffle(V)
        dist = dict(nx.all_pairs_shortest_path_length(F))
        C = []
        for v in V:
            if all(dist[v].get(c, 99) >= dmin for c in C):
                C.append(v)
            if len(C) == k:
                break
        if len(C) < k:
            continue
        NC = set(C) | {w for c in C for w in F[c]}
        Y = []
        for v in V:
            if len(Y) == ny:
                break
            if v in NC or v in Y:
                continue
            if all(dist[v].get(y, 99) >= 3 for y in Y):
                Y.append(v)
        if len(Y) < ny:
            continue
        K = nx.Graph(F)
        leaves = []
        for i, c in enumerate(C):
            K.add_edge(c, n + i)
            leaves.append(n + i)
        X = leaves + Y
        b = [K.degree(v) % 2 for v in range(K.number_of_nodes())]
        pairs = list(combinations(X, 2))
        r = L.sep(K, b, pairs)
        tot += 1
        if r is None:
            und += 1
        elif not r:
            bad += 1
            if bad <= 5:
                print("FAIL", n, sorted(F.edges()), "C", C, "Y", Y, flush=True)
    print(f"k={k} ny={ny} dmin={dmin}: total {tot} failures {bad} undecided {und}")


if __name__ == "__main__":
    main()

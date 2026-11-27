"""Adversarial search for L1 (Lovasz decomposition of an all-odd graph whose path at c avoids a
non-neighbour a) and its one-even-vertex variant L1e (F has exactly one even vertex a, which gets
no end; the path at an odd c, c not adjacent to a, avoids a).

Usage: python3 l1_search.py MODE trials [budget]
  MODE in: big (random all-odd F, n = 12..16), even (L1e, n = 5..11), glue (cut-vertex gluings)
"""
import random
import sys

import networkx as nx

import rd_lib as L
from lovasz_matching import make_all_odd


def fix_parity_except(G, rng, keep_even):
    """Toggle edges so every vertex except keep_even is odd (keep_even must end up even)."""
    for _ in range(200):
        bad = [v for v in G if (G.degree(v) % 2 == 0) != (v == keep_even)]
        if not bad:
            return True
        if len(bad) == 1:
            return False
        x, y = rng.sample(bad, 2)
        if G.has_edge(x, y):
            G.remove_edge(x, y)
        else:
            G.add_edge(x, y)
    return False


def main():
    mode = sys.argv[1]
    trials = int(sys.argv[2])
    if len(sys.argv) > 3:
        L.BUDGET = int(sys.argv[3])
        L.FINAL = False
    rng = random.Random(77)
    tot = bad = unk = 0
    for it in range(trials):
        if mode == "big":
            n = rng.choice([12, 14, 16])
            F = nx.gnp_random_graph(n, rng.uniform(0.15, 0.5), seed=rng.randrange(10 ** 9))
            if not make_all_odd(F, rng) or F.number_of_edges() > 110:
                continue
            b = [1] * n
            pairs = [(c, a) for c in F for a in F if c != a and not F.has_edge(c, a)]
            pairs = rng.sample(pairs, min(6, len(pairs)))
        elif mode == "even":
            n = rng.choice([5, 7, 9, 11])
            F = nx.gnp_random_graph(n, rng.uniform(0.2, 0.8), seed=rng.randrange(10 ** 9))
            a = 0
            if not fix_parity_except(F, rng, a) or F.degree(a) == 0:
                continue
            b = [0 if v == a else 1 for v in range(n)]
            pairs = [(c, a) for c in F if c != a and not F.has_edge(c, a) and F.degree(c) > 0]
        elif mode == "glue":
            # side 1: one-even-vertex graph on {a} + C; side 2: graph where a is odd; glue at a
            n1 = rng.choice([5, 7, 9])
            F1 = nx.gnp_random_graph(n1, rng.uniform(0.3, 0.9), seed=rng.randrange(10 ** 9))
            if not fix_parity_except(F1, rng, 0) or F1.degree(0) == 0:
                continue
            n2 = rng.choice([2, 4, 6])
            F2 = nx.gnp_random_graph(n2, rng.uniform(0.3, 0.9), seed=rng.randrange(10 ** 9))
            if not make_all_odd(F2, rng):
                continue
            F = nx.disjoint_union(F1, F2)
            F = nx.contracted_nodes(F, 0, n1, self_loops=False)
            F = nx.convert_node_labels_to_integers(nx.Graph(F))
            if any(F.degree(v) % 2 == 0 for v in F):
                continue
            n = F.number_of_nodes()
            b = [1] * n
            a = 0
            pairs = [(c, a) for c in range(1, n1) if not F.has_edge(c, a) and F.degree(c) > 0]
        else:
            raise SystemExit("mode?")
        for c, a in pairs:
            r = L.ext(F, b, c, {a})
            if r is None:
                unk += 1
                continue
            tot += 1
            if not r:
                bad += 1
                print("FAIL", mode, sorted(F.edges()), "c", c, "a", a, flush=True)
    print(f"{mode}: {tot} pairs, {bad} failures, {unk} unknown")


if __name__ == "__main__":
    main()

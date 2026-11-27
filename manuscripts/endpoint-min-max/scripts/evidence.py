"""Evidence table for conjecture EMM (endpoint min-max).

For every graph of each family and every half-set M of its even vertices, compare
    realisable : the simple profile of M is realised by exactly n/2 paths (exact oracle tools/realis.c)
    cut-feasible : every inequality (1) of ED Section 12.4 holds (tools/cutfeas.c).
EMM failures are cut-feasible half-sets that are not realisable; "unsound" counts realisable
half-sets that violate (1), which must be 0 because (1) is necessary.

Usage: python3 evidence.py [6] [8] [10] [bottleneck] [counterexamples] [blobs]   (default: all)
Each family is reported in full and restricted to minimum degree >= 3 (the range of EMM_3).
Cross-check: cutfeas.c is compared with tools/cut_test.py on every half-set of order 6.
"""
import itertools
import os
import sys
import time

import networkx as nx

import emm_lib as L
import cut_test


def row(name, graphs, min_degree=1):
    graphs = [G for G in graphs if min(d for _, d in G.degree()) >= min_degree]
    if min_degree > 1:
        name += f", min degree >= {min_degree}"
    t = time.time()
    feas = L.cut_feasible(graphs)
    halfsets = nonreal = fails = unsound = 0
    examples = []
    for G, F in zip(graphs, feas):
        R = L.realisable_halfsets(G)
        Ev = L.even_vertices(G)
        for M in itertools.combinations(Ev, len(Ev) // 2):
            M = frozenset(M)
            halfsets += 1
            nonreal += M not in R
            if M in F and M not in R:
                fails += 1
                examples.append(("EMM-FAIL", G.edges(), sorted(M)))
            if M in R and M not in F:
                unsound += 1
                examples.append(("UNSOUND", G.edges(), sorted(M)))
    print(f"| {name} | {len(graphs)} | {halfsets} ({nonreal} non-realisable) | {fails} | {unsound} |"
          f"   [{time.time() - t:.0f}s]", flush=True)
    for ex in examples[:5]:
        print("   ", ex)


def crosscheck():
    graphs = L.all_connected(6)
    for G, F in zip(graphs, L.cut_feasible(graphs)):
        prep = cut_test.prepare(G)
        k = G.number_of_nodes() // 2
        Ev = L.even_vertices(G)
        for M in itertools.combinations(Ev, len(Ev) // 2):
            b = {v: G.degree(v) % 2 for v in G}
            for v in M:
                b[v] = 2
            ok = cut_test.cut_ok(prep, b, k)[0] and all(G.degree(v) + b[v] <= 2 * k for v in G)
            assert ok == (frozenset(M) in F), (G.edges(), M)
    print("cross-check with tools/cut_test.py at order 6: agree", flush=True)


def blobs(n, count, seed):
    """Two random blobs (orders a + b = n) joined by 1-3 edges, minimum degree >= 3: cuts can bind."""
    import random
    rng = random.Random(seed)
    out = []
    while len(out) < count:
        a = rng.randint(4, n - 4)
        A = nx.gnp_random_graph(a, rng.choice([.6, .75, .9]), seed=rng.randrange(2**31))
        B = nx.gnp_random_graph(n - a, rng.choice([.6, .75, .9]), seed=rng.randrange(2**31))
        G = nx.disjoint_union(A, B)
        for _ in range(rng.randint(1, 3)):
            G.add_edge(rng.randrange(a), a + rng.randrange(n - a))
        if nx.is_connected(G) and min(d for _, d in G.degree()) >= 3 and len(L.even_vertices(G)) >= 2:
            out.append(G)
    return out


def row_cutfeasible_only(name, graphs):
    """Like row(), but calls the oracle only on cut-feasible half-sets (faster at order 12)."""
    t = time.time()
    feas = L.cut_feasible(graphs)
    halfsets = excluded = fails = 0
    for G, F in zip(graphs, feas):
        Ev = L.even_vertices(G)
        for M in itertools.combinations(Ev, len(Ev) // 2):
            halfsets += 1
            if frozenset(M) not in F:
                excluded += 1
                continue
            b = {v: G.degree(v) % 2 for v in G}
            for v in M:
                b[v] = 2
            if not L.realis.profile_ok(G, b):
                fails += 1
                print("   EMM3-FAIL", sorted(G.edges()), sorted(M), flush=True)
    print(f"| {name} | {len(graphs)} | {halfsets} ({excluded} cut-excluded) | {fails} | not tested |"
          f"   [{time.time() - t:.0f}s]", flush=True)


def counterexamples():
    """The order-12 counterexamples to EMM of missing-move Thm 7.5 (all have minimum degree <= 2)."""
    path = os.path.join(L.ROOT, "manuscripts", "missing-move", "scripts", "outputs", "emm_counterexamples12.g6")
    graphs = [L.relabel(nx.from_graph6_bytes(l.strip().encode())) for l in open(path) if l.strip()]
    print(f"order-12 counterexamples ({path}): minimum degrees {sorted(min(d for _, d in G.degree()) for G in graphs)}")
    row("12, counterexamples of missing-move Thm 7.5", graphs)


def main():
    which = sys.argv[1:] or ["6", "8", "10", "bottleneck", "counterexamples", "blobs"]
    crosscheck()
    print("| Order | Graphs | Half-sets | EMM failures | Unsound |")
    print("|---|---|---|---|---|")
    for w in which:
        if w in ("6", "8"):
            row(w, L.all_connected(int(w)))
            row(w, L.all_connected(int(w)), min_degree=3)
        elif w == "10":
            row("10, random G(10,p), seed 20261127", L.random_sample())
            row("10, random G(10,p), seed 20261127", L.random_sample(), min_degree=3)
        elif w == "bottleneck":
            row("6-10, bottleneck families", L.bottleneck())
            row("6-10, bottleneck families", L.bottleneck(), min_degree=3)
        elif w == "counterexamples":
            counterexamples()
        elif w == "blobs":
            row("10, two blobs joined by 1-3 edges, seed 10", blobs(10, 60, 10), min_degree=3)
            row_cutfeasible_only("12, two blobs joined by 1-3 edges, seed 12, min degree >= 3", blobs(12, 25, 12))


if __name__ == "__main__":
    main()

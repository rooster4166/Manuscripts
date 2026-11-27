"""Evidence table for conjecture EMM (endpoint min-max).

For every graph of each family and every half-set M of its even vertices, compare
    realisable : the simple profile of M is realised by exactly n/2 paths (exact oracle tools/realis.c)
    cut-feasible : every inequality (1) of ED Section 12.4 holds (tools/cutfeas.c).
EMM failures are cut-feasible half-sets that are not realisable; "unsound" counts realisable
half-sets that violate (1), which must be 0 because (1) is necessary.

Usage: python3 evidence.py [6] [8] [10] [bottleneck]      (default: all four rows)
Cross-check: cutfeas.c is compared with tools/cut_test.py on every half-set of order 6.
"""
import itertools
import sys
import time

import emm_lib as L
import cut_test


def row(name, graphs):
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


def main():
    which = sys.argv[1:] or ["6", "8", "10", "bottleneck"]
    crosscheck()
    print("| Order | Graphs | Half-sets | EMM failures | Unsound |")
    print("|---|---|---|---|---|")
    for w in which:
        if w in ("6", "8"):
            row(w, L.all_connected(int(w)))
        elif w == "10":
            row("10, random G(10,p), seed 20261127", L.random_sample())
        elif w == "bottleneck":
            row("6-10, bottleneck families", L.bottleneck())


if __name__ == "__main__":
    main()

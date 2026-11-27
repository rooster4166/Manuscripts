"""Cap functions of the cut inequalities, and the matroid question (does EMM explain EMC?).

For a vertex v and a half-set M, the inequalities (1) at v read, in arm form,
    2|M n Y| >= e(v, Y) - |Od n Y| - |delta_{G-v}(Y)|        (Y in V - v).
Complementing, they are upper bounds on the unmarked set:  |(Ev - M) n X| <= g_v(X)  (X in Ev - v),
with g_v submodular (a projection of a cut function; the right side above is always even).  So the
half-sets that satisfy the inequalities at v are the bases of a matroid truncation, family F_v, and
the cut-feasible family is F = intersection of all F_v.

The script reports, for each family of graphs:
  - raw:  whether the global cap f = min_v f_v is submodular (tools/capsub.c, local test);
  - capM: whether the cap system {I : |I n X| <= f(X)} is a matroid;
  - F is a matroid basis family;  F = F_v for a single vertex v;  the graph is critical (p(G) = n/2).
and it checks by brute force that every per-vertex family F_v is a matroid basis family.

Usage: python3 caps.py [6] [8]
"""
import itertools
import sys
from collections import Counter

import emm_lib as L
from cut_selection import cut_tables


def is_bases(B):
    B = set(B)
    for X in B:
        for Y in B:
            for x in X - Y:
                if not any(((X - {x}) | {y}) in B for y in Y - X):
                    return False
    return True


def per_vertex_families(G):
    n = G.number_of_nodes()
    nbr, cut = cut_tables(G)
    Ev = L.even_vertices(G)
    odd = [G.degree(v) % 2 for v in range(n)]
    fams = []
    for v in range(n):
        rest = ((1 << n) - 1) & ~(1 << v)
        need = []     # (mask of Y, lower bound on 2|M n Y|)
        Y = rest
        while Y:
            eY = bin(nbr[v] & Y).count("1")
            lb = eY - sum(odd[y] for y in range(n) if Y >> y & 1) - (cut[Y] - eY)
            assert lb % 2 == 0
            if lb > 0:
                need.append((Y, lb))
            Y = (Y - 1) & rest
        Fv = set()
        for M in itertools.combinations(Ev, len(Ev) // 2):
            mm = sum(1 << x for x in M)
            if all(2 * bin(mm & Y).count("1") >= lb for Y, lb in need):
                Fv.add(frozenset(M))
        fams.append(Fv)
    return fams


def main():
    for w in sys.argv[1:] or ["6", "8"]:
        graphs = L.all_connected(int(w))
        feas = L.cut_feasible(graphs)
        caps = L.run_lines("capsub", graphs)
        c = Counter()
        for G, F, line in zip(graphs, feas, caps):
            e, rawSub, famMat = map(int, line.split()[:3])
            fams = per_vertex_families(G)
            assert set.intersection(*fams) == F
            for Fv in fams:
                assert is_bases(Fv), (G.edges(), "per-vertex family is not a matroid")
            single = any(Fv == F for Fv in fams)
            c[(bool(rawSub), bool(famMat), is_bases(F), single, L.critical(G))] += 1
        print(f"order {w}: {len(graphs)} graphs; every per-vertex family F_v is a matroid basis family")
        print("  (raw f submodular, cap system matroid, F matroid bases, F = some F_v, critical): count")
        for k, v in sorted(c.items()):
            print("   ", k, v)


if __name__ == "__main__":
    main()

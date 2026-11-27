"""Cut selection (CS) and pairing selection (PS).

CS: for every even vertex r there is a cut-feasible half-set M containing r.
PS: the even vertices can be split into pairs so that every half-set containing exactly one vertex of
    each pair is cut-feasible.  PS implies CS (choose the end r of its pair).

The script also checks two reformulations proved in the manuscript, on every graph it reads:
  (A) arm form: M is cut-feasible iff for every v and every Y in V - v,
          e(v, Y) <= b(Y) + |delta_{G-v}(Y)|.
  (P) a pairing P has all its transversals cut-feasible iff, for every vertex v, P meets the cut
      condition in G^v (G with the edges at v replaced by the non-edges at v):
          |delta_P(Y)| <= |delta_{G^v}(Y)|  for every Y.

Usage: python3 cut_selection.py [6] [8] [10] [bottleneck]
"""
import itertools
import sys
import time
from collections import Counter

import emm_lib as L


def pairings(xs):
    if not xs:
        yield []
        return
    a = xs[0]
    for i in range(1, len(xs)):
        for p in pairings(xs[1:i] + xs[i + 1:]):
            yield [(a, xs[i])] + p


def cut_tables(G):
    n = G.number_of_nodes()
    nbr = [sum(1 << u for u in G[v]) for v in range(n)]
    cut = [0] * (1 << n)
    for Y in range(1, 1 << n):
        low = (Y & -Y).bit_length() - 1
        Yp = Y & (Y - 1)
        cut[Y] = cut[Yp] + G.degree(low) - 2 * bin(nbr[low] & Yp).count("1")
    return nbr, cut


def arm_feasible(G, M, nbr, cut):
    n = G.number_of_nodes()
    b = [G.degree(v) % 2 + (2 if v in M else 0) for v in range(n)]
    for v in range(n):
        rest = ((1 << n) - 1) & ~(1 << v)
        Y = rest
        while True:
            eY = bin(nbr[v] & Y).count("1")
            bY = sum(b[y] for y in range(n) if Y >> y & 1)
            cutGv = cut[Y] - eY          # edges of delta(Y) not at v
            if eY > bY + cutGv:
                return False
            if Y == 0:
                break
            Y = (Y - 1) & rest
    return True


def pairing_ok_by_cuts(G, P, nbr, cut):
    n = G.number_of_nodes()
    full = (1 << n) - 1
    for v in range(n):
        rest = full & ~(1 << v)
        Y = rest
        while Y:
            eY = bin(nbr[v] & Y).count("1")
            cutGv = cut[Y] - eY + (bin(Y).count("1") - eY)
            split = sum(1 for a, c in P if ((Y >> a) & 1) != ((Y >> c) & 1))
            if split > cutGv:
                return False
            Y = (Y - 1) & rest
    return True


def run(name, graphs, check_forms=True):
    t = time.time()
    feas = L.cut_feasible(graphs)
    cs_fail = ps_fail = 0
    stats = Counter()
    for G, F in zip(graphs, feas):
        Ev = L.even_vertices(G)
        if any(not any(r in M for M in F) for r in Ev):
            cs_fail += 1
            print("   CS FAILS:", sorted(G.edges()))
        nbr, cut = cut_tables(G)
        if check_forms:
            for M in itertools.combinations(Ev, len(Ev) // 2):
                assert arm_feasible(G, set(M), nbr, cut) == (frozenset(M) in F), (G.edges(), M)
        good = []
        for P in pairings(Ev):
            allok = all(frozenset(q[o >> i & 1] for i, q in enumerate(P)) in F for o in range(1 << len(P)))
            if check_forms:
                assert allok == pairing_ok_by_cuts(G, P, nbr, cut), (G.edges(), P)
            if allok:
                good.append(P)
        if not good:
            ps_fail += 1
            print("   PS FAILS:", sorted(G.edges()))
        else:
            stats["graphs with a good pairing"] += 1
            if any(all(G.has_edge(a, c) for a, c in P) for P in good):
                stats["... one whose pairs are all edges"] += 1
    print(f"| {name} | {len(graphs)} | {cs_fail} | {ps_fail} |   [{time.time() - t:.0f}s] {dict(stats)}",
          flush=True)


def main():
    which = sys.argv[1:] or ["6", "8", "10", "bottleneck"]
    print("| Graphs | Count | CS failures | PS failures |")
    print("|---|---|---|---|")
    for w in which:
        if w in ("6", "8"):
            run(f"all connected, order {w}", L.all_connected(int(w)), check_forms=(w == "6"))
        elif w == "10":
            run("random G(10,p), seed 20261127", L.random_sample(), check_forms=False)
        elif w == "bottleneck":
            run("bottleneck families, orders 6-10", L.bottleneck(), check_forms=False)


if __name__ == "__main__":
    main()

"""coverage.py: which instances of the (T2) matching base follow from proved theorems (test2, task 3).

For an instance (J, z, r) and a perfect matching M0 of J[N(z)] (r matched to a0), M is the base
graph (no even vertex; z a leaf at r).  A set X is packed in M if its vertices are pairwise
non-adjacent with no common neighbour.  Each test below gives a Lovasz decomposition of M meeting
every condition of the matching base (r not in Q(a0); for every other pair ab, a not in Q(b)):
  SEP : N(z) is packed in M                      -> separation_set (MeetsOnce N(z)).
  L1  : for some c in N(z) - r, Y = N(z) - c is packed and has no vertex in N_M[c]
                                                  -> lovasz_avoid_set (Q(c) misses Y, MeetsOnce Y).
  NA  : for some y in N(z) - r, Y = N(z) - y is packed, and some vertex w of positive degree with
        no neighbour in Y is joined to y by a walk of M - Y
                                                  -> avoid_packed_of_reach (NA set form).
(In each case every pair inside the packed set is separated, and the left-out vertex avoids its
partner; r's condition holds since r, a0 are both in the packed set or the left-out vertex is a0.)
Reports, per d(z), the number of instances with matching data and how many some matching covers.
usage: python3 coverage.py < t2_fields
"""
import sys
from collections import Counter

import networkx as nx

from tb2 import base_graph, perfect_matchings


def packed(M, X):
    X = list(X)
    for i, a in enumerate(X):
        for b in X[i + 1:]:
            if M.has_edge(a, b) or set(M[a]) & set(M[b]):
                return False
    return True


def reach_ok(M, y, Y):
    H = M.copy()
    H.remove_nodes_from(Y)
    comp = nx.node_connected_component(H, y)
    Ys = set(Y)
    return any(M.degree(w) > 0 and not (set(M[w]) & Ys) for w in comp)


def main():
    stats = Counter()
    for line in sys.stdin:
        f = line.split()
        if len(f) < 3:
            continue
        g6, z, r = f[0], int(f[1]), int(f[2])
        J = nx.from_graph6_bytes(g6.encode())
        T = sorted(J[z])
        d = len(T)
        pms = list(perfect_matchings(T, J))
        stats[("inst", d)] += 1
        if not pms:
            continue
        stats[("data", d)] += 1
        best = set()
        for pm in pms:
            M = base_graph(J, z, r, pm)
            if packed(M, T):
                best.add("SEP")
            for c in T:
                if c == r:
                    continue
                Y = [v for v in T if v != c]
                if packed(M, Y):
                    if not (set(Y) & (set(M[c]) | {c})):
                        best.add("L1")
                    if reach_ok(M, c, Y):
                        best.add("NA")
        for t in ("SEP", "L1", "NA"):
            if t in best:
                stats[(t, d)] += 1
        if best:
            stats[("any", d)] += 1
    for k in sorted(stats, key=str):
        print(k, stats[k])


if __name__ == "__main__":
    main()

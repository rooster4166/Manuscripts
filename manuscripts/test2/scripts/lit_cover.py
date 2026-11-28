"""lit_cover.py: (T2) instances settled by published floor theorems on B = J - z (test2, Section 3).

The even vertices of B = J - z are exactly N(z) - r, so the E-subgraph of B is K = J[N(z) - r].
  PYBER : K is a forest                                  -> p(B) <= floor(|B|/2)  [Pyber]
  FAN   : every block of K is triangle-free, max degree <= 3 -> p(B) <= floor(|B|/2) [Fan]
(both as restated with the floor in Botler-Sambinelli and Bonamy-Perrett; see
research/notes/eulerian-gallai-literature.md).  Either gives (T2) by one split at r.
Also counted: SEMI (B an odd semi-clique: OSB Thm 4).  Reports per d(z).
usage: python3 lit_cover.py < t2_fields
"""
import sys
from collections import Counter

import networkx as nx


def fan_ok(K):
    for comp in nx.biconnected_components(K):
        H = K.subgraph(comp)
        if H.number_of_edges() == 0:
            continue
        if max(d for _, d in H.degree()) > 3:
            return False
        if any(t for t in nx.triangles(H).values()):
            return False
    return True


def semi(B):
    N = B.number_of_nodes()
    if N % 2 == 0:
        return False
    k = (N - 1) // 2
    return N * (N - 1) // 2 - B.number_of_edges() < k


stats = Counter()
for line in sys.stdin:
    f = line.split()
    if len(f) < 3:
        continue
    J = nx.from_graph6_bytes(f[0].encode())
    z, r = int(f[1]), int(f[2])
    d = J.degree(z)
    K = J.subgraph([v for v in J[z] if v != r])
    B = J.copy()
    B.remove_node(z)
    stats[("inst", d)] += 1
    py = nx.is_forest(K) if K.number_of_edges() else True
    fa = fan_ok(K)
    if py:
        stats[("PYBER", d)] += 1
    if fa:
        stats[("FAN", d)] += 1
    if semi(B):
        stats[("SEMI", d)] += 1
    if not fa and not semi(B):
        stats[("neither", d)] += 1
for k in sorted(stats, key=str):
    print(k, stats[k])

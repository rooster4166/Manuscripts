"""cones.py: the (T2) instances of cones (test2 session, task 4).

J = B + u (u joined to every vertex of B) with |B| = N odd.  The even vertices of J are the odd
vertices of B, so (T2) instances at non-apex vertices are exactly: B has exactly two odd vertices
a ~ x, and the test is at (J, a, x) (and (J, x, a)).  Reads t2.c lines (fields) and reports, for the
instances where J has a universal vertex outside {z, r}: counts, slack (= floor for J - z), and the
shape of B (degree of a, number of odd vertices of C = B - a).
usage: python3 cones.py < t2_fields
"""
import sys
from collections import Counter

import networkx as nx

stats = Counter()
for line in sys.stdin:
    f = line.split()
    if len(f) < 9:
        continue
    g6, z, r = f[0], int(f[1]), int(f[2])
    n, slack, t2 = int(f[5]), int(f[6]), int(f[7])
    J = nx.from_graph6_bytes(g6.encode())
    univ = [u for u in J if J.degree(u) == n - 1 and u not in (z, r)]
    if not univ:
        continue
    stats[("cone instances", n)] += 1
    stats[("slack", n, slack)] += 1
    stats[("t2", n, t2)] += 1
    B = J.copy()
    B.remove_node(univ[0])
    oddB = sorted(v for v in B if B.degree(v) % 2 == 1)
    assert oddB == sorted((z, r)) and B.has_edge(z, r), (g6, z, r)
    stats[("d_B(a)", n, B.degree(z))] += 1
    if len(univ) > 1:
        stats[("several universal", n)] += 1
for k in sorted(stats, key=str):
    print(k, stats[k])

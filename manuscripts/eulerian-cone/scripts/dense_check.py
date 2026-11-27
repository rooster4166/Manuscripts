"""dense_check.py RE_PROFILE_ORACLE FILE...: checks marked-reduction Cor 168 and Thm 170 (project
collection, unrefereed) on every connected Eulerian graph F of even order 2k in the files.

Cor 168: for every k-set R of vertices of degree 2k-2, the end profile "2 at each vertex of R, 0
elsewhere" is realisable (by exactly k paths).
Thm 170: for every (k-1)-set R of vertices of degree 2k-2 and every vertex v outside R of positive
degree, the profile "2 at each vertex of R + v, 0 elsewhere" is realisable.
Profiles are decided exactly by tools/route_ext.c (query P).  Also reports how many roots r with
p_r = k (tight) lie in graphs with at least k-1 vertices of degree 2k-2 (covered by Thm 170).
"""
import itertools
import subprocess
import sys

import networkx as nx

oracle = sys.argv[1]
lines, meta = [], []
graphs = 0
cover = 0
for fn in sys.argv[2:]:
    for l in open(fn):
        F = nx.from_graph6_bytes(l.strip().encode())
        n = F.number_of_nodes()
        k = n // 2
        if n % 2:
            continue
        graphs += 1
        H = [v for v in F if F.degree(v) == n - 2]
        E = list(F.edges())
        head = "P %d %d %s" % (n, len(E), " ".join("%d %d" % e for e in E))
        if len(H) >= k:
            for R in itertools.combinations(H, k):
                b = [2 if v in R else 0 for v in range(n)]
                lines.append(head + " " + " ".join(map(str, b)))
                meta.append(("Cor168", l.strip(), R))
        if len(H) >= k - 1:
            cover += 1
            for R in itertools.combinations(H, k - 1):
                for v in F:
                    if v in R or F.degree(v) == 0:
                        continue
                    b = [2 if (u in R or u == v) else 0 for u in range(n)]
                    lines.append(head + " " + " ".join(map(str, b)))
                    meta.append(("Thm170", l.strip(), R + (v,)))
out = subprocess.run([oracle], input="\n".join(lines) + "\n", capture_output=True,
                     text=True).stdout.split()
assert len(out) == len(lines)
from collections import Counter
c = Counter()
for (kind, g6, R), o in zip(meta, out):
    c[(kind, o)] += 1
    if o != "1":
        print("NOT REALISED", kind, g6, R, o)
print("graphs", graphs, "with >= k-1 vertices of degree n-2:", cover)
print(dict(c))

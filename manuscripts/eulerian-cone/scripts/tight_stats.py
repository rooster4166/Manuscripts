"""tight_stats.py FILE...: statistics of the tight roots (p_r = k) in re.c -m output.

For each root: degree d(r); the trivial lower bound d(r)/2 + 1 (r is an end of two paths and
every other path at r uses two of its edges); whether p_r = k; whether the bound is attained.
Prints a table by (n, d(r)) and lists the tight roots whose degree bound is below k.
"""
import sys
from collections import Counter

import networkx as nx

tab = Counter()
unforced = []
for fn in sys.argv[1:]:
    for line in open(fn):
        g6, rest = line.split(None, 1)
        f = rest.split()
        r, p, k, st = int(f[0]), int(f[1]), int(f[2]), f[3]
        B = nx.from_graph6_bytes(g6.encode())
        n = B.number_of_nodes()
        d = B.degree(r)
        if st != "OK":
            tab[(n, d, "UNK")] += 1
            continue
        tight = p == k
        tab[(n, d, "tight" if tight else "slack")] += 1
        if tight and d // 2 + 1 < k:
            unforced.append((g6, r, d, p, k))
print("n d(r) status count")
for key in sorted(tab):
    print(*key, tab[key])
print("tight roots with d(r)/2 + 1 < k:", len(unforced))
for u in unforced[:40]:
    print(*u)

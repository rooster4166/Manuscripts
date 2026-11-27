"""summary.py: the numbers of Section 6 from the compact tables in ../data/out (*.tab.gz).

For the exhaustive minimum-mode tables (2-connected Eulerian graphs of even order <= 10): roots,
tight roots (p_r = n/2) split by the reason the counting bound is tight, p_r = CB, p_r > CB.
The 8 order-10 roots whose minimum the solver did not certify (status UNK) are listed; their
values are settled in the text (7 by CB = n/2, one by an unbudgeted search and CP-SAT).
"""
import gzip
import math
import sys
from collections import Counter

import networkx as nx

sys.argv = ["x"]
exec(open(__file__.replace("summary.py", "countbound.py")).read().split("cnt = Counter()")[0])

for n in (4, 6, 8, 10):
    c = Counter()
    graphs = set()
    for line in gzip.open("../data/out/re_%d_min.tab.gz" % n, "rt"):
        g6, r, p, k, st = line.split()
        r, p, k = int(r), int(p), int(k)
        graphs.add(g6)
        B = nx.from_graph6_bytes(g6.encode())
        degs = [d for _, d in B.degree()]
        c["roots"] += 1
        cbv = cb(degs, B.degree(r))
        if st != "OK":
            c["UNK"] += 1
            c["UNK with CB=k"] += cbv == k
            continue
        c["p=CB"] += p == cbv
        c["p>CB"] += p > cbv
        if p == k:
            c["tight"] += 1
            m = B.number_of_edges()
            if B.degree(r) == n - 2:
                c["tight: d(r)=n-2"] += 1
            elif math.ceil(m / (n - 1)) == k:
                c["tight: edge count"] += 1
            else:
                c["tight: other counting"] += 1
            c["tight with CB<k"] += cbv < k
    print("n=%d graphs=%d" % (n, len(graphs)), dict(c))

"""uc_check.py FILE...: test RE* and UC on re.c -x output (exact p_r, with witnesses).

RE*:  p_r(B) <= ceil(n/2)                          (implied by Gallai's conjecture)
UC:   p_r(B) <= max(CB(B, r), ceil(n/2) - 1)       (CB = end-counting bound, countbound.py)
Reports counts by order, by parity and 2-connectivity, and every UC violation.
"""
import sys
from collections import Counter

import networkx as nx

sys.argv, files = sys.argv[:1], sys.argv[1:]
exec(open(__file__.replace("uc_check.py", "countbound.py")).read().split("cnt = Counter()")[0])

cnt = Counter()
viol = []
for fn in files:
    for line in open(fn):
        g6, rest = line.split(None, 1)
        f = rest.split()
        r, p, k, st = int(f[0]), int(f[1]), int(f[2]), f[3]
        B = nx.from_graph6_bytes(g6.encode())
        n = B.number_of_nodes()
        bic = nx.is_biconnected(B) if n >= 3 else False
        key = (n, "2conn" if bic else "conn")
        if st not in ("OK", "OVER"):
            cnt[key + ("UNK",)] += 1
            continue
        c = cb([d for _, d in B.degree()], B.degree(r))
        ce = (n + 1) // 2
        cnt[key + ("RE*ok" if p <= ce else "RE*FAIL",)] += 1
        if p <= max(c, ce - 1):
            cnt[key + ("UCok",)] += 1
        else:
            cnt[key + ("UCFAIL",)] += 1
            viol.append((g6, r, p, c, n))
for key in sorted(cnt):
    print(*key, cnt[key])
print("UC violations:", len(viol))
for v in viol[:30]:
    print(*v)

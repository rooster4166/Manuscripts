"""verify_uc.py: independent check of the lines printed by re.c -u (UC mode, with witnesses).

Line format: 'g6 r size ceil(n/2) STATUS cb=CB | path | path | ...'.
STATUS UC: the witness has size <= max(CB, ceil(n/2) - 1) (UC holds at the root);
STATUS OK / OKUNK: size <= ceil(n/2) (RE* holds; UC failed or was undecided within the budget).
Every witness is checked: paths of the graph, edge partition, size as printed, an end at r
(two if every degree is even), and CB recomputed independently (countbound.py).
Prints counts per status; exits with an error on the first failure.
"""
import sys
from collections import Counter

import networkx as nx

sys.argv, files = sys.argv[:1], sys.argv[1:]
exec(open(__file__.replace("verify_uc.py", "countbound.py")).read().split("cnt = Counter()")[0])

cnt = Counter()
for line in sys.stdin:
    line = line.strip()
    if not line or line.startswith("#"):
        continue
    g6, tail = line.split(None, 1)
    head, *rest = tail.split("|")
    f = head.split()
    r, size, ce, st, cbf = int(f[0]), int(f[1]), int(f[2]), f[3], f[4]
    B = nx.from_graph6_bytes(g6.encode())
    c = cb([d for _, d in B.degree()], B.degree(r))
    assert cbf == "cb=%d" % c, (line[:60], c)
    if st not in ("UC", "OK", "OKUNK"):
        cnt[st] += 1
        continue
    paths = [list(map(int, s.split())) for s in rest if s.strip()]
    assert len(paths) == size, line[:80]
    used, ends = set(), Counter()
    for P in paths:
        assert len(P) >= 2 and len(set(P)) == len(P)
        for x, y in zip(P, P[1:]):
            e = frozenset((x, y))
            assert B.has_edge(x, y) and e not in used
            used.add(e)
        ends[P[0]] += 1
        ends[P[-1]] += 1
    assert len(used) == B.number_of_edges()
    assert ends[r] >= (2 if all(d % 2 == 0 for _, d in B.degree()) else 1)
    if st == "UC":
        assert size <= max(c, ce - 1)
    else:
        assert size <= ce
    cnt[st] += 1
print(dict(cnt))

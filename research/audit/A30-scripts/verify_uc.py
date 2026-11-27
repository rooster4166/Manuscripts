"""A30 audit: verify re.c -u output lines WITH witnesses (run without -m/-q).
Checks: witness is a decomposition into paths, r is an end of >= 2 paths, and the size is
<= max(CB, ceil(n/2)-1) for status UC (CB recomputed here), <= ceil(n/2) for status OK."""
import sys
from collections import Counter
import networkx as nx

def CB(degs, dr):
    p = 1
    while True:
        c = [min(d, 2*p-d) for d in degs]
        if min(dr, 2*p-dr) >= 2 and min(c) >= 0 and sum(c) >= 2*p: return p
        p += 1

cnt = Counter()
for line in sys.stdin:
    line = line.strip()
    if not line or line.startswith('#'): continue
    g6, tail = line.split(None, 1)
    head, *rest = tail.split('|')
    f = head.split(); r, got, ce, st = int(f[0]), int(f[1]), int(f[2]), f[3]
    B = nx.from_graph6_bytes(g6.encode())
    if st not in ('UC', 'OK', 'OKUNK'): cnt[st] += 1; continue
    paths = [list(map(int, s.split())) for s in rest if s.strip()]
    used = set(); ends = Counter()
    for P in paths:
        assert len(P) >= 2 and len(set(P)) == len(P)
        for x, y in zip(P, P[1:]):
            e = frozenset((x, y)); assert B.has_edge(x, y) and e not in used; used.add(e)
        ends[P[0]] += 1; ends[P[-1]] += 1
    assert len(used) == B.number_of_edges() and ends[r] >= 2 and len(paths) == got
    cb = CB([d for _, d in B.degree()], B.degree(r))
    n = B.number_of_nodes()
    if st == 'UC': assert got <= max(cb, (n + 1)//2 - 1); cnt['UC verified'] += 1
    else: assert got <= (n + 1)//2; cnt[st + ' verified (RE only)'] += 1
print(dict(cnt))

"""countbound.py FILE...: compare p_r (re.c -m output) with the end-counting bound CB(B, r).

In a decomposition of an Eulerian graph into p paths with e_v ends at v, the vertex v lies on
(d_v + e_v)/2 paths, so e_v <= 2p - d_v; also e_v <= d_v; sum e_v = 2p; e_r >= 2 at the root.
CB(B, r) is the least p for which such numbers e_v (even, >= 0) exist, i.e.
    2p - d_r >= 2   and   sum_v min(d_v, 2p - d_v) >= 2p   (with d_v <= 2p for all v).
Reports: how often p_r = CB, and every root with p_r = k (tight) but CB < k.
"""
import sys
from collections import Counter

import networkx as nx


def cb(degs, dr):
    p = 1
    while True:
        if 2 * p - dr >= 2 and all(d <= 2 * p for d in degs):
            cap = sum(min(d, 2 * p - d) for d in degs)
            if cap >= 2 * p:
                return p
        p += 1


cnt = Counter()
bad = []
for fn in sys.argv[1:]:
    for line in open(fn):
        g6, rest = line.split(None, 1)
        f = rest.split()
        r, p, k, st = int(f[0]), int(f[1]), int(f[2]), f[3]
        if st != "OK":
            cnt["unk"] += 1
            continue
        B = nx.from_graph6_bytes(g6.encode())
        degs = [d for _, d in B.degree()]
        c = cb(degs, B.degree(r))
        assert c <= p, (g6, r, c, p)
        cnt["p=CB" if p == c else "p>CB"] += 1
        if p == k:
            cnt["tight"] += 1
            if c < k:
                bad.append((g6, r, p, c, k))
print(dict(cnt))
print("tight roots with CB < k:", len(bad))
for b in bad[:20]:
    print(*b)

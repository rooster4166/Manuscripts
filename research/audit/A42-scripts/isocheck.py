"""A42: check that a graph6 list is pairwise non-isomorphic, and that every graph is connected
and has all degrees odd.  Invariant: sorted multiset of per-vertex (degree, A^2..A^5 diagonal,
sorted neighbour degrees); collisions are resolved by an exact backtracking isomorphism test."""
import sys, collections
import numpy as np
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import g6dec, comp_of

def inv(n, adj):
    M = np.zeros((n, n), dtype=np.int64)
    for u in range(n):
        for v in adj[u]: M[u, v] = 1
    P = [M]
    for _ in range(4): P.append(P[-1] @ M)
    rows = []
    for v in range(n):
        rows.append((len(adj[v]),) + tuple(int(P[k][v, v]) for k in range(1, 5)) +
                    tuple(int(P[k][v].sum()) for k in range(4)) + tuple(sorted(len(adj[w]) for w in adj[v])))
    return tuple(sorted(rows))

def iso(n, A, B):
    da = [len(a) for a in A]; db = [len(b) for b in B]
    if sorted(da) != sorted(db): return False
    order = sorted(range(n), key=lambda v: -da[v])
    m = {}; used = set()
    def rec(k):
        if k == n: return True
        v = order[k]
        for w in range(n):
            if w in used or db[w] != da[v]: continue
            if all((u in A[v]) == (m[u] in B[w]) for u in m):
                m[v] = w; used.add(w)
                if rec(k + 1): return True
                del m[v]; used.discard(w)
        return False
    return rec(0)

G = [l.strip() for l in open(sys.argv[1]) if l.strip()]
buckets = collections.defaultdict(list); bad = 0
for g in G:
    n, adj = g6dec(g)
    if any(len(a) % 2 == 0 for a in adj) or len(comp_of(adj, 0)) != n: bad += 1
    buckets[inv(n, adj)].append(g)
coll = [b for b in buckets.values() if len(b) > 1]
isopairs = 0
for b in coll:
    for i in range(len(b)):
        for j in range(i + 1, len(b)):
            n, A = g6dec(b[i]); _, B = g6dec(b[j])
            if iso(n, A, B): isopairs += 1; print('ISOMORPHIC', b[i], b[j])
print('graphs', len(G), 'not connected-all-odd', bad, 'invariant classes', len(buckets),
      'colliding buckets', len(coll), 'isomorphic pairs', isopairs)

"""Small sanity check of the path-cycle facts used in the note.

Q = (0,...,m-1) is a path (m <= 6) and C a cycle, edge-disjoint from Q, with
contact set K = V(Q) cap V(C) nonempty.  Vertices of Q outside K are off C.
C is described by the cyclic order of K and, for each arc between consecutive
contacts, whether it is direct or has interior vertices (all off Q).  Interior
vertices are compressed to one (two when |K| = 1); a direct arc may not
duplicate an edge of Q, and when |K| = 2 the two arcs cannot both be direct.
We check:
  (L1')  |K| <= 4  ==> Q u C splits into two paths;
  (L1'') |K| = 5 and C has a vertex outside Q ==> two paths;
  (L6)   |K| = 6 and C has a vertex outside Q ==> two paths;
and list the configurations with C inside V(Q) that fail (expected: the
pentagram at five contacts, the edge-count obstructions at six).
"""
import itertools
from decomp import paths_at_most

def configs(m):
    Q = [(i, i + 1) for i in range(m - 1)]
    Qset = {frozenset(e) for e in Q}
    for r in range(1, m + 1):
        for K in itertools.combinations(range(m), r):
            first, rest = K[0], K[1:]
            seen = set()
            for perm in itertools.permutations(rest):
                order = (first,) + perm
                if r >= 3 and order[1] > order[-1]:
                    continue  # reflection
                arcs = [(order[i], order[(i + 1) % r]) for i in range(r)] if r >= 2 else [(first, first)]
                for sub in itertools.product((0, 1), repeat=len(arcs)):
                    if r == 1 and not sub[0]:
                        continue
                    if r == 2 and not (sub[0] or sub[1]):
                        continue
                    if any((not s) and frozenset(a) in Qset for s, a in zip(sub, arcs)):
                        continue
                    edges = list(Q)
                    nv = m
                    for s, (a, b) in zip(sub, arcs):
                        if r == 1:
                            edges += [(a, nv), (nv, nv + 1), (nv + 1, a)]; nv += 2
                        elif s:
                            edges += [(a, nv), (nv, b)]; nv += 1
                        else:
                            edges.append((a, b))
                    yield K, order, sub, edges, any(sub)

for m in range(1, 7):
    if m == 1:
        continue
    stats = {}
    bad = []
    for K, order, sub, edges, outside in configs(m):
        ok = paths_at_most(edges, 2)
        key = (len(K), outside)
        s = stats.setdefault(key, [0, 0]); s[0] += 1
        if not ok:
            s[1] += 1
            bad.append((K, order, sub))
    print(f"|V(Q)|={m}: (contacts, C has outside vertex) -> [configs, failures]: {dict(sorted(stats.items()))}")
    for b in bad:
        print("    fails:", b)

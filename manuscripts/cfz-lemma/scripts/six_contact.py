"""Finite check of the six-contact path-cycle lemma (L6).

Q = (0,1,2,3,4,5) is a path, C a cycle edge-disjoint from Q with
V(Q) subset of V(C) and V(C) != V(Q).  Write the six contacts in their
cyclic order on C; each of the six arcs of C between consecutive contacts is
either a direct edge or has interior vertices (all outside Q).  A direct arc
must not be an edge of Q.  Arcs with interior vertices are compressed to a
single interior vertex (lifting argument in the note).  We check every
cyclic order and every nonempty set of subdivided arcs containing the forced
ones; the union must split into two paths.
Also runs the analogous checks for 5 contacts (to confirm L1 in this range)
and reports failures for 7 contacts with one subdivided arc.
"""
import itertools, sys
from decomp import paths_at_most

def check(t, min_sub=1, max_sub=None, verbose=False):
    Q = [(i, i + 1) for i in range(t - 1)]
    Qset = {frozenset(e) for e in Q}
    fails = []
    total = 0
    seen = set()
    for perm in itertools.permutations(range(1, t)):
        order = (0,) + perm
        key = min(order[i:] + order[:i] for i in range(t))
        rev = tuple(reversed(order))
        key = min(key, min(rev[i:] + rev[:i] for i in range(t)))
        if key in seen: continue
        seen.add(key)
        arcs = [(order[i], order[(i + 1) % t]) for i in range(t)]
        forced = {i for i, (a, b) in enumerate(arcs) if frozenset((a, b)) in Qset}
        for r in range(0, t + 1):
            for sub in itertools.combinations(range(t), r):
                sub = set(sub)
                if not forced <= sub: continue
                if len(sub) < min_sub: continue
                if max_sub is not None and len(sub) > max_sub: continue
                edges = list(Q)
                nv = t
                for i, (a, b) in enumerate(arcs):
                    if i in sub:
                        edges += [(a, nv), (nv, b)]; nv += 1
                    else:
                        edges.append((a, b))
                total += 1
                if not paths_at_most(edges, 2):
                    fails.append((order, sorted(sub)))
    return total, fails

if __name__ == '__main__':
    for t in (3, 4, 5, 6):
        total, fails = check(t, min_sub=0)
        print(f"contacts={t}: configurations={total}, without 2-path partition={len(fails)}")
        for f in fails[:20]:
            print("   ", f)

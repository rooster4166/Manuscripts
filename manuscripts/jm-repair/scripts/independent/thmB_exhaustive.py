# Written by an independent internal referee agent (Nov 2026); copied here for reproducibility.
"""Independent check of Theorem B by direct search (no flow, no records).
Enumerate all decompositions of K_m into n labelled linear forests (up to vertex
relabelling is NOT used; we use a cheap colour-canonicalisation only when safe),
then for every admissible (U, c) (T = rest) search directly for an extension."""
import itertools, sys
from functools import lru_cache

def lf_ok(nv, edges):
    deg = [0]*nv; par = list(range(nv))
    def f(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    for u, v in edges:
        deg[u] += 1; deg[v] += 1
        if deg[u] > 2 or deg[v] > 2: return False
        a, b = f(u), f(v)
        if a == b: return False
        par[a] = b
    return True

def decomps(m, n):
    E = list(itertools.combinations(range(m), 2))
    # DFS assigning colours with incremental linear-forest check
    col = [None]*len(E)
    deg = [[0]*m for _ in range(n)]
    comp = [list(range(m)) for _ in range(n)]  # naive labels
    out = []
    def rec(idx):
        if idx == len(E):
            out.append(tuple(col)); return
        u, v = E[idx]
        for i in range(n):
            if deg[i][u] >= 2 or deg[i][v] >= 2: continue
            lab = comp[i]
            if lab[u] == lab[v]: continue
            old = lab[:]; a, b = lab[u], lab[v]
            for w in range(m):
                if lab[w] == a: lab[w] = b
            deg[i][u] += 1; deg[i][v] += 1; col[idx] = i
            rec(idx+1)
            deg[i][u] -= 1; deg[i][v] -= 1; comp[i] = old
            # comp[i] reassigned: need local alias refresh
        col[idx] = None
    # the alias issue: rewrite rec with explicit copies
    def rec2(idx, comps):
        if idx == len(E):
            out.append(tuple(col)); return
        u, v = E[idx]
        for i in range(n):
            if deg[i][u] >= 2 or deg[i][v] >= 2: continue
            lab = comps[i]
            if lab[u] == lab[v]: continue
            a, b = lab[u], lab[v]
            nl = tuple(b if w == a else w for w in lab)
            nc = comps[:i] + (nl,) + comps[i+1:]
            deg[i][u] += 1; deg[i][v] += 1; col[idx] = i
            rec2(idx+1, nc)
            deg[i][u] -= 1; deg[i][v] -= 1
        col[idx] = None
    rec2(0, tuple(tuple(range(m)) for _ in range(n)))
    return E, out

def extension_exists(m, n, E, colv, c, delta):
    """Direct DFS over (chi(xv), chi(yv)), v in V; checks linear forests on m+2 vertices."""
    x, y = m, m+1
    deg = [[0]*(m+2) for _ in range(n)]
    for (u, v), i in zip(E, colv):
        deg[i][u] += 1; deg[i][v] += 1
    deg[c][x] += 1; deg[c][y] += 1
    # component labels per colour
    labs = []
    for i in range(n):
        lab = list(range(m+2))
        for (u, v), j in zip(E, colv):
            if j == i:
                a, b = lab[u], lab[v]
                lab = [b if w == a else w for w in lab]
        if i == c:
            a, b = lab[x], lab[y]; lab = [b if w == a else w for w in lab]
        labs.append(tuple(lab))
    a = [0]*n
    def add(lab, u, v):
        if lab[u] == lab[v]: return None
        p, q = lab[u], lab[v]
        return tuple(q if w == p else w for w in lab)
    def rec(vi, labs):
        if vi == m:
            return all(a[i] >= delta[i] for i in range(n))
        rem = 2*(m - vi)
        need = sum(max(0, delta[i]-a[i]) for i in range(n))
        if need > rem: return False
        for i in range(n):
            if deg[i][vi] >= 2 or deg[i][x] >= 2: continue
            l1 = add(labs[i], vi, x)
            if l1 is None: continue
            deg[i][vi] += 1; deg[i][x] += 1; a[i] += 1
            labs1 = labs[:i] + (l1,) + labs[i+1:]
            for j in range(n):
                if deg[j][vi] >= 2 or deg[j][y] >= 2: continue
                l2 = add(labs1[j], vi, y)
                if l2 is None: continue
                deg[j][vi] += 1; deg[j][y] += 1; a[j] += 1
                ok = rec(vi+1, labs1[:j] + (l2,) + labs1[j+1:])
                deg[j][vi] -= 1; deg[j][y] -= 1; a[j] -= 1
                if ok:
                    deg[i][vi] -= 1; deg[i][x] -= 1; a[i] -= 1
                    return True
            deg[i][vi] -= 1; deg[i][x] -= 1; a[i] -= 1
        return False
    return rec(0, tuple(labs))

def main(n, m):
    k = 2*n + 1 - m
    assert k >= 4
    E, D = decomps(m, n)
    cnt = 0; fails = []
    seen = set()
    for colv in D:
        p = [m - sum(1 for j in colv if j == i) for i in range(n)]
        if max(p) > k: continue
        for usz in range(1, (k-2)//2 + 1):
            for U in itertools.combinations(range(n), usz):
                if any(p[i] > k-1 for i in U): continue
                for c in U:
                    S = [i for i in U if i != c]
                    T = [i for i in range(n) if i not in U]
                    delta = [0]*n
                    for i in T: delta[i] = max(0, p[i]+4-k)
                    delta[c] = max(0, p[c]+3-k)
                    for i in S: delta[i] = max(0, p[i]+5-k)
                    # colour-type signature dedupe: same multiset of (type,colour-class) up to colour perm
                    key = (tuple(sorted((('T' if i in T else ('c' if i == c else 'S')),
                                         tuple(sorted(e for e, j in zip(E, colv) if j == i))) for i in range(n))))
                    if key in seen: continue
                    seen.add(key)
                    cnt += 1
                    if not extension_exists(m, n, E, colv, c, delta):
                        fails.append((colv, U, c))
    print(f"n={n} m={m} k={k}: decomps={len(D)} instances(dedup colour-perm)={cnt} fails={len(fails)}")
    if fails: print(fails[:5])

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))

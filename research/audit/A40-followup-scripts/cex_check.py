"""cex_check.py -- independent check of the two counterexamples of ln.tex Sec. 7 (commit 61abb4e).

For each example: build the graph from the edge list as stated in ln.tex, check the stated even
vertex, the leaf-tail conditions of ln Definition 2.2 (leaf of degree one, heads far apart), the
non-sparseness of the heads, print graph6 (to compare with audit A40), and enumerate ALL parity
decompositions (one end at each odd vertex, none at the even vertex) by exact cover with simple
paths.  Reports how many keep every tail.  Shares no code with lnsolve.c / lnlib.py.
usage: python3 cex_check.py
"""
import itertools

def g6(n, edges):
    bits = []
    E = set(frozenset(e) for e in edges)
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if frozenset((i, j)) in E else 0)
    while len(bits) % 6: bits.append(0)
    s = chr(n + 63)
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k + 6]: v = 2 * v + b
        s += chr(v + 63)
    return s

def all_paths(n, adj):
    """all simple paths with >= 1 edge, each once (as vertex tuples with first < last)"""
    out = []
    def ext(P, S):
        if len(P) >= 2 and P[0] < P[-1]: out.append(tuple(P))
        for y in adj[P[-1]]:
            if y not in S:
                S.add(y); P.append(y); ext(P, S); P.pop(); S.discard(y)
    for v in range(n): ext([v], {v})
    return out

def decomps(n, edges, adj, req):
    eidx = {frozenset(e): k for k, e in enumerate(edges)}
    paths = []
    for P in all_paths(n, adj):
        mask = 0
        for a, b in zip(P, P[1:]): mask |= 1 << eidx[frozenset((a, b))]
        paths.append((P, mask))
    by_low = {}
    for P, mask in paths:
        low = (mask & -mask).bit_length() - 1
        by_low.setdefault(low, []).append((P, mask))
    full = (1 << len(edges)) - 1
    res = []
    def rec(used, chosen, ends):
        if used == full:
            if all(ends[v] == req[v] for v in range(n)): res.append(list(chosen))
            return
        low = (~used & full)
        low = (low & -low).bit_length() - 1
        for P, mask in by_low.get(low, []):
            if mask & used: continue
            a, b = P[0], P[-1]
            if ends[a] + 1 > req[a] or ends[b] + 1 > req[b]: continue
            ends[a] += 1; ends[b] += 1; chosen.append(P)
            rec(used | mask, chosen, ends)
            chosen.pop(); ends[a] -= 1; ends[b] -= 1
    rec(0, [], [0] * n)
    return res

def check(name, n, edges, tails, even_claim):
    adj = [set() for _ in range(n)]
    for a, b in edges: adj[a].add(b); adj[b].add(a)
    deg = [len(x) for x in adj]
    ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
    print('==', name, 'n=%d m=%d g6=%s' % (n, len(edges), g6(n, edges)))
    print('  degrees', deg, 'even vertices', ev, 'claimed', even_claim, 'OK' if ev == [even_claim] else 'MISMATCH')
    for c, A in tails:
        okleaf = deg[c] == 1
        far = all(a != c and a not in adj[c] and not (adj[a] & adj[c]) for a in A)
        print('  tail (%d,%s): leaf deg 1: %s, far apart: %s' % (c, sorted(A), okleaf, far))
    H = set().union(*[set(A) for c, A in tails])
    witnesses = [v for v in range(n) if len(adj[v] & H) >= 2]
    print('  heads', sorted(H), 'sparse:', not witnesses, '(vertices with >= 2 head neighbours: %s)' % witnesses)
    leaves = {c for c, A in tails}
    print('  some tail avoids another tail\'s leaf:', any((set(A) & (leaves - {c})) for c, A in tails))
    print('  connected:', connected(n, adj))
    req = [d % 2 for d in deg]
    D = decomps(n, edges, adj, req)
    keep = [d for d in D if all(not (set(P) & set(A)) for c, A in tails for P in d if c in P)]
    print('  parity decompositions: %d; keeping all tails: %d -> %s' % (len(D), len(keep), 'UNSAT' if not keep else 'SAT'))
    # deletion-minimality of the tail family (drop one head at a time)
    for c, A in tails:
        for a in sorted(A):
            T2 = [(c2, (set(A2) - {a}) if c2 == c else set(A2)) for c2, A2 in tails]
            k2 = [d for d in D if all(not (set(P) & set(A2)) for c2, A2 in T2 for P in d if c2 in P)]
            print('    drop head %d from tail %d: %s' % (a, c, 'SAT' if k2 else 'UNSAT'))
    return D, keep

def connected(n, adj):
    seen = {0}; st = [0]
    while st:
        v = st.pop()
        for w in adj[v]:
            if w not in seen: seen.add(w); st.append(w)
    return len(seen) == n

if __name__ == '__main__':
    e7 = [(0, 3), (0, 5), (0, 6), (1, 4), (1, 5), (1, 6), (2, 6), (3, 5)]
    check('order 7 (ln.tex l. 433)', 7, e7, [(2, {5}), (4, {0, 2})], 3)
    e9 = [(0, 4), (1, 5), (2, 6)] + [(v, w) for v in (0, 1, 2, 3) for w in (7, 8)] + [(7, 8)]
    check('order 9 (ln.tex ll. 435-437)', 9, e9, [(4, {1, 2, 3}), (5, {0, 2, 3}), (6, {0, 1, 3})], 3)

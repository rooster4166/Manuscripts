#!/usr/bin/env python3
"""examples.py (audit A34): independent re-verification of Examples 8.2 and 8.3 of trn.tex.
Pure Python, no use of the authors' code.  For each example: the graph (from the edge list in the
text, cross-checked against the graph6 name), the TRN/core/N-witness conditions, the stated D',
its forced chain and transfer (sequential re-routing as in Section 2), and all four repair moves
(exch, rot, rep, loc) by brute force, plus existence of a good decomposition of G."""
import sys, itertools

def g6(n, E):
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (i, j) in E or (j, i) in E else 0)
    while len(bits) % 6: bits.append(0)
    return chr(n + 63) + ''.join(chr(63 + int(''.join(map(str, bits[k:k + 6])), 2)) for k in range(0, len(bits), 6))

def adjof(n, E):
    A = [set() for _ in range(n)]
    for a, b in E: A[a].add(b); A[b].add(a)
    return A

def decomps(n, A, need=None):
    """all path decompositions with end count need[v] (default deg mod 2); paths as tuples.
    Method: take the smallest vertex that still needs an end and grow its path in all ways."""
    E = {frozenset((a, b)) for a in range(n) for b in A[a]}
    if need is None: need = [len(A[v]) % 2 for v in range(n)]
    out = []
    def rec(rem, need, acc):
        if not rem:
            if not any(need): out.append(list(acc))
            return
        vs = [v for v in range(n) if need[v]]
        if not vs: return
        a = vs[0]
        def grow(path, rem):
            cur = path[-1]
            for w in sorted({w for e in rem if cur in e for w in e if w != cur}):
                if w in path: continue
                e = frozenset((cur, w)); r2 = rem - {e}; p2 = path + [w]
                if need[w]:
                    nd = list(need); nd[a] -= 1; nd[w] -= 1
                    rec(r2, nd, acc + [tuple(p2)])
                grow(p2, r2)
        grow([a], rem)
    rec(frozenset(E), list(need), [])
    # each decomposition is produced once per ordering of its paths' start vertices: dedupe
    seen, res = set(), []
    for D in out:
        key = frozenset(p if p[0] < p[-1] else tuple(reversed(p)) for p in D)
        if key not in seen: seen.add(key); res.append(D)
    return res

def is_lovasz(n, A, D, need=None):
    if need is None: need = [len(A[v]) % 2 for v in range(n)]
    used = set(); ends = [0] * n
    for p in D:
        if len(p) < 2 or len(set(p)) != len(p): return False
        for a, b in zip(p, p[1:]):
            e = frozenset((a, b))
            if b not in A[a] or e in used: return False
            used.add(e)
        ends[p[0]] += 1; ends[p[-1]] += 1
    allE = {frozenset((a, b)) for a in range(n) for b in A[a]}
    return used == allE and ends == list(need)

def path_at(D, v):
    P = [p for p in D if p[0] == v or p[-1] == v]
    assert len(P) == 1, (v, D)
    p = P[0]
    return list(p) if p[0] == v else list(reversed(p))

def fan(D, g, u):
    """sequential re-routing exactly as in Section 2 (paths of D' ending at x_j, current version)."""
    D = [list(p) for p in D]
    orig = {}
    for i, p in enumerate(D):
        for v in (p[0], p[-1]): orig[v] = i
    chain = [g]
    while True:
        x = chain[-1]; i = orig[x]; p = D[i]
        if p[0] != x: p.reverse()
        if u not in p:
            D[i] = [u] + p; return D, chain
        k = p.index(u); nx = p[k - 1]
        D[i] = list(reversed(p[:k])) + p[k:]
        assert nx not in chain
        chain.append(nx)

def check(name, n, E, g, y, x, u, Dp, good_example=None):
    print(f'=== {name}: graph6 {g6(n, E)}, g={g} y={y} x={x} u={u}')
    A = adjof(n, E); deg = [len(A[v]) for v in range(n)]
    ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
    print('  degrees', deg, 'even vertices', ev)
    assert ev == [g] and deg[x] % 2 and deg[y] % 2 and x != y and x not in A[y] and u in A[g] and u in A[y] and u != x
    tight = all(v in A[y] for v in A[g] if v not in (x, y))
    cwit = [w for w in A[y] if w != u and w not in A[x]]
    gwit = [w for w in A[y] if w != g and w not in A[x]]
    cn = sorted(A[x] & A[y])
    ind = deg[g] == 2 and not (lambda a, b: b in A[a])(*sorted(A[g]))
    print(f'  (C2) all-tight={tight}  (C3) child witnesses={cwit}  (C4) common nbrs={cn}  (C5) not-indep={not ind}')
    print(f'  N-witness of G itself (w in N(y), w != g, w !~ x): {gwit}  -> {"reached" if gwit else "NOT reached"} by the induction of Theorem 5.2')
    K = adjof(n, [e for e in E if set(e) != {g, u}])
    Dp = [tuple(p) for p in Dp]
    ok = is_lovasz(n, K, Dp); Q = path_at(Dp, y)
    print(f'  D\' = {Dp}: Lovasz decomposition of K: {ok}; Q\'(y) = {Q}; good: {x not in Q}')
    assert ok and x not in Q
    P0 = path_at(Dp, g); print(f'  P_0 = {P0}')
    R, ch = fan(Dp, g, u); QR = path_at(R, y)
    print(f'  chain = {ch}; transfer = {R}; Lovasz in G: {is_lovasz(n, A, R)}; Q(y) = {QR}; bad: {x in QR}')
    # exch hypothesis
    Py = [p for p in Dp if any({a, b} == {y, u} for a, b in zip(p, p[1:]))][0]
    print(f'  exch hypothesis (u notin Q\'(y), V(P_y) cap V(Q\'(y)) = {{y}}): {u not in Q and set(Py) & set(Q) == {y}}')
    # loc: union of chain paths + Q'(y) + gu
    sel = []
    for v in ch:
        p = tuple(path_at(Dp, v)); key = frozenset(p)
        if key not in [frozenset(s) for s in sel]: sel.append(p)
    if frozenset(Q) not in [frozenset(s) for s in sel]: sel.append(tuple(Q))
    UE = [(a, b) for p in sel for a, b in zip(p, p[1:])] + [(g, u)]
    U = adjof(n, UE)
    locs = decomps(n, U)
    loc_ok = [D for D in locs if x not in path_at(D, y)]
    print(f'  loc: union of {len(sel)} paths + gu has {len(locs)} decompositions; with y\'s path avoiding x: {len(loc_ok)}')
    for D in locs: print('     ', D, ' y-path', path_at(D, y))
    # rot: every rotation at y along any path through y, then plain Fan
    rot_ok = 0; rots = 0
    for p in Dp:
        if tuple(Q) in (p, tuple(reversed(p))) or y not in p: continue
        k = p.index(y)
        if k in (0, len(p) - 1): continue
        for half, oth in ((p[k:], p[:k + 1]), (tuple(reversed(p[:k + 1])), tuple(reversed(p[k:])))):
            J = list(oth) + Q[1:]
            if len(set(J)) != len(J) or x in half: continue
            D2 = [q for q in Dp if q != p and set(q) != set(Q) or (q != p and tuple(q) != tuple(Q) and tuple(q) != tuple(reversed(Q)))]
            D2 = [q for q in Dp if q != p and frozenset(q) != frozenset(Q)] + [tuple(half), tuple(J)]
            assert is_lovasz(n, K, D2)
            rots += 1
            R2, _ = fan(D2, g, u)
            if x not in path_at(R2, y): rot_ok += 1
    print(f'  rot: {rots} valid good rotations, {rot_ok} with a good transfer')
    # rep: every re-pairing of the halves at u
    halves = []; rest = []
    for p in Dp:
        if u not in p: rest.append(p); continue
        k = p.index(u); halves.append(list(p[:k + 1])); halves.append(list(reversed(p[k:])))
    def matchings(idx):
        if not idx: yield []; return
        a = idx[0]
        for b in idx[1:]:
            if set(halves[a]) & set(halves[b]) == {u}:
                for m in matchings([c for c in idx if c not in (a, b)]): yield [(a, b)] + m
    reps = rep_ok = 0
    for M in matchings(list(range(len(halves)))):
        D2 = list(rest) + [tuple(halves[a] + list(reversed(halves[b]))[1:]) for a, b in M]
        assert is_lovasz(n, K, D2)
        if x in path_at(D2, y): continue
        reps += 1
        R2, _ = fan(D2, g, u)
        if x not in path_at(R2, y): rep_ok += 1
    print(f'  rep: {reps} good re-pairings, {rep_ok} with a good transfer')
    # TRN: some good decomposition of G; and keeping all paths of D' outside the chain paths and Q'(y)
    allG = decomps(n, A)
    goodG = [D for D in allG if x not in path_at(D, y)]
    kept = [p for p in Dp if frozenset(p) not in [frozenset(s) for s in sel]]
    keepG = [D for D in goodG if all(any(tuple(q) in (tuple(p), tuple(reversed(p))) for q in D) for p in kept)]
    print(f'  G: {len(allG)} Lovasz decompositions, {len(goodG)} good; good ones keeping {kept}: {len(keepG)}')
    if good_example is not None:
        Dg = [tuple(p) for p in good_example]
        okg = is_lovasz(n, K, Dg); Qg = path_at(Dg, y); P0g = path_at(Dg, g)
        Rg, chg = fan(Dg, g, u)
        print(f'  stated good D\' {Dg}: Lovasz in K {okg}, Q\'(y)={Qg} avoids x {x not in Qg}, P_0={P0g} avoids u {u not in P0g}, chain {chg}, Q(y)={path_at(Rg, y)}')
    return dict(loc=len(loc_ok), rot=rot_ok, rep=rep_ok, exch=(u not in Q and set(Py) & set(Q) == {y}), trn=len(goodG))

if __name__ != '__main__':
    raise SystemExit
# Example 8.2
check('Ex 8.2 FsObO', 7, [(0,1),(0,2),(0,3),(1,4),(1,6),(2,5),(2,6),(4,6)], 4, 1, 2, 6,
      [(1,0), (2,5), (3,0,2,6,1,4)], good_example=[(1,4), (0,1,6,2), (3,0,2,5)])
# Example 8.3 (first)
check('Ex 8.3 FsQnO', 7, [(0,1),(0,2),(0,3),(0,5),(0,6),(1,4),(1,6),(2,5),(2,6),(4,5),(4,6)], 6, 5, 1, 4,
      [(5,0), (1,6,0,2), (3,0,1,4,5,2,6)])
# Example 8.3 (second)
check('Ex 8.3 FsRLO', 7, [(0,1),(0,2),(0,3),(0,5),(0,6),(1,4),(1,5),(2,6),(4,5),(4,6)], 2, 1, 6, 0,
      [(1,4), (2,6,4,5,1,0,3), (5,0,6)])
# A reached analogue of Example 8.2 (y ~ g, d(g) = 2 on the triangle g y u, G has an N-witness)
check('suggested replacement FqJPo', 7, [(0,1),(0,2),(0,5),(1,3),(1,5),(2,4),(2,6),(3,5),(3,6),(4,6)], 4, 2, 3, 6,
      [(0,1,3), (1,5,3,6,2,4), (2,0,5)])

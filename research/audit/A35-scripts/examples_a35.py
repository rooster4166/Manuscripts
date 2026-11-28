#!/usr/bin/env python3
"""examples_a35.py (audit A35): independent check of Examples 6.6, 6.11, 9.2, 9.3 of trn.tex
(the steering claims; the residual claims of 9.2 and 9.3 are rechecked by A34-scripts/examples.py).
Pure Python; uses only exec_sched.py of this directory (no code of the authors).
usage: python3 -I examples_a35.py"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from exec_sched import parse_g6, fan_step, check_parity, run

def g6(n, E):
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (i, j) in E or (j, i) in E else 0)
    while len(bits) % 6: bits.append(0)
    return chr(n + 63) + ''.join(chr(63 + int(''.join(map(str, bits[k:k + 6])), 2)) for k in range(0, len(bits), 6))

def all_decomps(edges, verts):
    """every parity decomposition (each exactly once), paths oriented from their least odd end."""
    out = []
    def rec(E, acc):
        if not E:
            out.append(list(acc)); return
        d = {}
        for e in E:
            for v in e: d[v] = d.get(v, 0) + 1
        odd = sorted(v for v in d if d[v] % 2)
        if not odd: return
        w = odd[0]
        def grow(path, rem):
            c = path[-1]
            for z in sorted(z for e in rem if c in e for z in e if z != c):
                if z in path: continue
                r2 = rem - {frozenset((c, z))}; p2 = path + [z]
                if d[z] % 2:
                    acc.append(p2); rec(r2, acc); acc.pop()
                grow(p2, r2)
        grow([w], E)
    rec(frozenset(edges), [])
    return out

def path_at(D, v):
    Q = [P for P in D if P[0] == v or P[-1] == v]
    assert len(Q) == 1
    return Q[0] if Q[0][0] == v else Q[0][::-1]

def core_test(n, adj, g, y, x, u):
    deg = [len(adj[v]) for v in range(n)]
    ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
    trn = ev == [g] and deg[x] % 2 == 1 and deg[y] % 2 == 1 and x != y and x not in adj[y] \
        and u in adj[g] and u in adj[y] and u != x
    c0 = any(w != g and w not in adj[x] for w in adj[y])
    c2 = all(v in adj[y] for v in adj[g] if v not in (x, y))
    c3 = any(w != u and w not in adj[x] for w in adj[y])
    c4 = bool(adj[x] & adj[y])
    c5 = not (deg[g] == 2 and sorted(adj[g])[1] not in adj[sorted(adj[g])[0]])
    E = {frozenset((a, b)) for a in range(n) for b in adj[a]}
    K = E - {frozenset((g, u))}
    Ds = all_decomps(K, range(n))
    goodD = [D for D in Ds if x not in path_at(D, y)]
    return dict(trn=trn, c0=c0, c2=c2, c3=c3, c4=c4, c5=c5, child_good=bool(goodD), nD=len(Ds), ngood=len(goodD)), goodD

def first_moves(n, adj, g, y, x):
    """legal first moves in G+ (Definition 6.3)."""
    L = n
    A = [set(s) for s in adj] + [set()]
    A[y].add(L); A[L].add(y)
    res = []
    for t, p, o in ((0, g, y), (1, y, g)):
        for q in sorted(A[p]):
            if q in (x, L) or q == o: continue
            if o in A[q] - {p}: continue
            res.append((t, p, q))
    return res

def construction_outputs(n, adj, g, y, x, moves):
    """all decompositions of G that the proof of Theorem 6.5 produces from the schedule, over every
    choice of bottom decomposition whose l-path avoids x."""
    L = n
    E = {frozenset((a, b)) for a in range(n) for b in adj[a]} | {frozenset((y, L))}
    cur = set(E); levels = []
    for (t, a, q) in moves:
        levels.append(set(cur)); cur.discard(frozenset((a, q)))
    outs = set()
    for D in all_decomps(cur, range(n + 1)):
        if x in [P for P in D if L in P][0]: continue
        D2 = [list(P) for P in D]; c2 = cur
        for (t, a, q), prev in zip(reversed(moves), reversed(levels)):
            D2 = fan_step(D2, a, q); c2 = prev
            check_parity(D2, c2, list(range(n + 1)))
            assert all(not (L in P and x in P) for P in D2)
        P = [P for P in D2 if L in P][0]; D2.remove(P)
        if P[-1] == L: P = P[::-1]
        D2.append(P[1:])
        outs.add(frozenset(tuple(P) if P[0] < P[-1] else tuple(P[::-1]) for P in D2))
    return outs

def canon(D):
    return frozenset(tuple(P) if P[0] < P[-1] else tuple(P[::-1]) for P in D)

def sched_line(name, g, y, x, moves):
    return 'SCHED %s %d %d %d %s' % (name, g, y, x, ' '.join('%d:%d-%d' % m for m in moves))

ok = True
def claim(text, cond):
    global ok
    print(('  OK   ' if cond else '  FAIL ') + text)
    ok &= bool(cond)

# ---------------- Example 6.6 ----------------
print('Example 6.6 (FsRDG)')
EL = [(0,1),(0,2),(0,3),(0,5),(0,6),(1,4),(1,5),(2,6),(5,6)]
claim('graph6 of the edge list is FsRDG', g6(7, EL) == 'FsRDG')
n, adj = parse_g6('FsRDG'); g, y, x, u = 2, 0, 4, 6
info, _ = core_test(n, adj, g, y, x, u)
claim('N(g) = {0,6}, triangle g y u', adj[g] == {0, 6} and 6 in adj[0])
claim('core test: %s' % info, all(info[k] for k in ('trn', 'c0', 'c2', 'c3', 'c4', 'c5', 'child_good')))
mv = [(1, 0, 1), (0, 2, 0), (0, 0, 3)]
run(sched_line('FsRDG', g, y, x, mv), True)
claim('schedule y:0->1, g:2->0, g:0->3 is legal and its construction verifies', True)
L = 7
E = {frozenset((a, b)) for a in range(n) for b in adj[a]} | {frozenset((y, L))}
bottom = E - {frozenset((0, 1)), frozenset((0, 2)), frozenset((0, 3))}
claim('bottom graph = 05,06,0l,14,15,26,56', bottom == {frozenset(e) for e in [(0,5),(0,6),(0,L),(1,4),(1,5),(2,6),(5,6)]})
dg = {v: sum(1 for e in bottom if v in e) for v in range(8)}
claim('bottom has the single even vertex 1', [v for v in range(8) if dg[v] and dg[v] % 2 == 0] == [1])
D = [[0, 5], [L, 0, 6], [2, 6, 5, 1, 4]]
check_parity(D, bottom, list(range(8)))
claim('stated bottom decomposition is a parity decomposition, l-path avoids 4', 4 not in D[1])
D3 = fan_step(D, 0, 3); E3 = bottom | {frozenset((0, 3))}; check_parity(D3, E3, list(range(8)))
claim('step 3 gives 3 0 5: %s' % D3, canon(D3) == canon([[3, 0, 5], [L, 0, 6], [2, 6, 5, 1, 4]]))
D2 = fan_step(D3, 2, 0); E2 = E3 | {frozenset((0, 2))}; check_parity(D2, E2, list(range(8)))
claim('step 2 gives 0 2 6 5 1 4: %s' % D2, canon(D2) == canon([[3, 0, 5], [L, 0, 6], [0, 2, 6, 5, 1, 4]]))
D1 = fan_step(D2, 0, 1); E1 = E2 | {frozenset((0, 1))}; check_parity(D1, E1, list(range(8)))
claim('step 1 gives 5 6 2 0 1 4 and 1 5 0 3: %s' % D1, canon(D1) == canon([[1, 5, 0, 3], [L, 0, 6], [5, 6, 2, 0, 1, 4]]))
outs = construction_outputs(n, adj, g, y, x, mv)
claim('final {1503, 06, 562014} is among the %d construction outputs' % len(outs),
      canon([[1, 5, 0, 3], [0, 6], [5, 6, 2, 0, 1, 4]]) in outs)

# ---------------- Example 6.11 ----------------
print('Example 6.11 (FqHTg)')
EL = [(0,1),(0,2),(0,6),(1,3),(1,5),(2,4),(2,6),(3,5),(3,6),(5,6)]
claim('graph6 of the edge list is FqHTg', g6(7, EL) == 'FqHTg')
n, adj = parse_g6('FqHTg'); g, y, x = 6, 1, 2
claim('N(g)={0,2,3,5}, N(y)={0,3,5}, N(x)={0,4,6}', adj[g] == {0,2,3,5} and adj[y] == {0,3,5} and adj[x] == {0,4,6})
for u in (0, 3, 5):
    info, goodD = core_test(n, adj, g, y, x, u)
    claim('u=%d core test: %s' % (u, {k: v for k, v in info.items()}), all(info[k] for k in ('trn', 'c0', 'c2', 'c3', 'c4', 'c5', 'child_good')))
    if u == 0:
        ntr = 0
        for Dp in goodD:
            R = fan_step(Dp, g, u)
            if x not in path_at(R, y): ntr += 1
        claim('u=0: %d good D\', %d transfer (paper: 36, 24)' % (len(goodD), ntr), (len(goodD), ntr) == (36, 24))
        Dp = [[1, 3, 5], [2, 0, 1, 5, 6, 3], [4, 2, 6]]
        K = {frozenset((a, b)) for a in range(n) for b in adj[a]} - {frozenset((6, 0))}
        check_parity(Dp, K, list(range(n)))
        R = fan_step(Dp, g, u)
        claim('stated D\' good, trivial chain (P_0 = %s avoids u), Q(y) = %s' % (path_at(Dp, g), path_at(R, y)),
              x not in path_at(Dp, y) and u not in path_at(Dp, g) and path_at(R, y) == [1, 3, 5])
claim('no legal first move: %s' % first_moves(n, adj, g, y, x), first_moves(n, adj, g, y, x) == [])
# Dqw at order 5
n5, adj5 = parse_g6('Dqw')
E5 = sorted((a, b) for a in range(n5) for b in adj5[a] if a < b)
print('  Dqw edges', E5)
deg5 = [len(adj5[v]) for v in range(n5)]; g5 = [v for v in range(n5) if deg5[v] and deg5[v] % 2 == 0][0]
found = []
for y5 in range(n5):
    for x5 in range(n5):
        if x5 == y5 or deg5[x5] % 2 == 0 or deg5[y5] % 2 == 0 or x5 in adj5[y5]: continue
        cores = []
        for u5 in sorted(adj5[g5] & adj5[y5] - {x5}):
            info, _ = core_test(n5, adj5, g5, y5, x5, u5)
            if all(info[k] for k in ('trn', 'c0', 'c2', 'c3', 'c4', 'c5', 'child_good')): cores.append(u5)
        if cores: found.append((y5, x5, cores, first_moves(n5, adj5, g5, y5, x5)))
print('  Dqw core triples (y, x, core u, legal first moves):', found)
claim('Dqw has 6 edges and a core triple with a legal first move', len(E5) == 6 and any(f[3] for f in found))

# ---------------- Example 9.2 ----------------
print('Example 9.2 (FqJPo)')
n, adj = parse_g6('FqJPo'); g, y, x, u = 4, 2, 3, 6
info, _ = core_test(n, adj, g, y, x, u)
claim('core test: %s' % info, all(info[k] for k in ('trn', 'c0', 'c2', 'c3', 'c4', 'c5', 'child_good')))
mv = [(1, 2, 0), (0, 4, 2), (0, 2, 6), (0, 6, 4)]
run(sched_line('FqJPo', g, y, x, mv), True)
claim('schedule y:2->0, g:4->2->6->4 is legal (retires at 4) and its construction verifies', True)
outs = construction_outputs(n, adj, g, y, x, mv)
target = canon([[5, 0, 1, 3], [0, 2, 4, 6, 3, 5, 1], [6, 2]])
claim('stated output {5013, 0246351, 62} is among the %d construction outputs %s' % (len(outs), sorted(sorted(o) for o in outs)), target in outs)

# ---------------- Example 9.3 ----------------
print('Example 9.3 (FsQnO, FsRLO)')
n, adj = parse_g6('FsQnO'); g, y, x, u = 6, 5, 1, 4
info, _ = core_test(n, adj, g, y, x, u)
claim('FsQnO core test: %s' % info, all(info[k] for k in ('trn', 'c0', 'c2', 'c3', 'c4', 'c5', 'child_good')))
claim('FsQnO: N(y) = %s inside N(g) = %s, no legal first move' % (adj[y], adj[g]), adj[y] <= adj[g] and first_moves(n, adj, g, y, x) == [])
n, adj = parse_g6('FsRLO'); g, y, x, u = 2, 1, 6, 0
info, _ = core_test(n, adj, g, y, x, u)
claim('FsRLO core test: %s, d(y) = %d' % (info, len(adj[y])), all(info[k] for k in ('trn', 'c0', 'c2', 'c3', 'c4', 'c5', 'child_good')) and len(adj[y]) == 3)
mv = [(1, 1, 4), (0, 2, 0), (0, 0, 3)]
run(sched_line('FsRLO', g, y, x, mv), True)
claim('FsRLO schedule y:1->4, g:2->0->3 is legal and its construction verifies', True)
print('ALL OK' if ok else 'SOME CLAIM FAILED')

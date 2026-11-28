#!/usr/bin/env python3
"""mt_verify.py: independent executor for k-token schedules (session claude/multi-token).

Reads SCHED lines of mtok.cpp:
    SCHED g6 resid z r w y1,x1 y2,x2 ... | moves
(resid = 1: g6 is B = J - z with N(z) = {0..5}, z gets index |B|).  Moves: Mp-u (a token moves),
Di (tail i is dropped), Sp:a-b (the token p of degree 2 is suppressed).  For each line it executes
the proof of the transfer theorem (manuscript Theorem 2.7) and of Theorem 3.1, sharing no code with
mtok.cpp:
  1. builds J, checks that z is the only even vertex, r, w in N(z), and that the pairs form a
     perfect matching of J[N(z) - {r, w}]; builds M and the leaf graph M+ (leaf n+i at y_i);
  2. replays the moves, re-deriving the legality of each one from Definition 2.2 (tokens = even
     vertices of the current graph; X = {l_i, x_i : i live});
  3. at the bottom checks <= 1 even vertex and <= 1 live tail, and gets a parity decomposition with
     no path through l_i and x_i (live i) from the oracle route_ext (query WS), which it re-checks;
  4. undoes the moves in reverse order: a suppression by subdividing the edge ab, a drop by adding
     the path l_i y_i, a move p -> u by Fan's forced chain (own implementation below), checking
     Fan's hypothesis b(p) = 1, Z(u) empty, and after every step that the object is a parity
     decomposition of the graph at that level meeting every live {l_i, x_i} at most once;
  5. deletes the leaves and checks that the result is a Lovasz decomposition of M with x_i not on
     Q(y_i) for every i (the triangle base);
  6. lifts it to Test1 with tb.py's lift (direct-test1, Steps 1-2) and verify_test1.
usage: mt_verify.py ROUTE_EXT < sched.txt
"""
import sys
import os
import subprocess

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'direct-test1', 'scripts'))
import networkx as nx  # noqa: E402
from tb import lift, verify_test1  # noqa: E402


def g6_adj(s):
    G = nx.from_graph6_bytes(s.encode())
    n = G.number_of_nodes()
    A = [set(G.neighbors(v)) for v in range(n)]
    return n, A


def even(A, v):
    return len(A[v]) > 0 and len(A[v]) % 2 == 0


def ends_of(D):
    e = {}
    for P in D:
        for v in (P[0], P[-1]):
            e[v] = e.get(v, 0) + 1
    return e


def check_parity(A, D, live_pairs, where):
    """D is a parity decomposition of the graph A meeting every pair at most once."""
    used = set()
    for P in D:
        assert len(P) >= 2 and len(set(P)) == len(P), (where, 'not a path', P)
        for a, b in zip(P, P[1:]):
            e = frozenset((a, b))
            assert b in A[a] and e not in used, (where, 'bad edge', P, a, b)
            used.add(e)
    m = sum(len(s) for s in A) // 2
    assert len(used) == m, (where, 'edges not covered', len(used), m)
    en = ends_of(D)
    for v in range(len(A)):
        assert en.get(v, 0) == len(A[v]) % 2, (where, 'ends != deg mod 2 at', v)
    for (c, x) in live_pairs:
        for P in D:
            assert not (c in P and x in P), (where, 'a path meets', c, x, P)


def fan(D, t, w):
    """Fan's forced chain: add the edge tw to D (t has one end, every neighbour of w has an end)."""
    D = [list(P) for P in D]
    endpath = {}
    for i, P in enumerate(D):
        for v in (P[0], P[-1]):
            assert v not in endpath, 'two ends at a vertex'
            endpath[v] = i
    x, seen = t, set()
    while True:
        assert x not in seen, 'chain repeats'
        seen.add(x)
        i = endpath[x]
        P = D[i]
        if P[-1] == x:
            P = P[::-1]
        assert P[0] == x, 'chain vertex is not an end of its path'
        if w not in P:
            D[i] = [w] + P
            return D
        k = P.index(w)
        y = P[k - 1]
        D[i] = P[:k][::-1] + P[k:]
        x = y


def oracle_bottom(ora, A, live_pairs):
    N = len(A)
    E = sorted({(min(a, b), max(a, b)) for a in range(N) for b in A[a]})
    b = [len(A[v]) % 2 for v in range(N)]
    q = "WS %d %d %s %s %d %s" % (N, len(E), " ".join("%d %d" % e for e in E), " ".join(map(str, b)),
                                 len(live_pairs), " ".join("%d %d" % p for p in live_pairs))
    out = subprocess.run([ora], input=q + "\n", capture_output=True, text=True).stdout.strip()
    assert out.startswith('1'), ('bottom not solvable by the oracle', out[:40])
    parts = out.split('|')[1:-1]
    return [list(map(int, s.split())) for s in parts]


def check(ora, line):
    head, mvs = line.rsplit(' |', 1)
    p = head.split()
    g6, resid, z, r, w = p[1], int(p[2]), int(p[3]), int(p[4]), int(p[5])
    pairs = [tuple(map(int, s.split(','))) for s in p[6:]]          # (y_i, x_i)
    n, A = g6_adj(g6)
    if resid:
        assert z == n
        A.append(set(range(6)))
        for u in range(6):
            A[u].add(z)
        n += 1
    J = nx.Graph()
    J.add_nodes_from(range(n))
    J.add_edges_from((a, b) for a in range(n) for b in A[a] if a < b)
    assert [v for v in range(n) if len(A[v]) % 2 == 0] == [z], 'z is not the only even vertex'
    Nz = set(A[z])
    assert r in Nz and w in Nz and r != w
    pv = [v for pr in pairs for v in pr]
    assert len(set(pv)) == len(pv) and set(pv) == Nz - {r, w}, 'not a perfect matching of N(z)-{r,w}'
    for y, x in pairs:
        assert x in A[y], 'pair is not an edge of J'
    k = len(pairs)
    # M and M+
    M = [set(s) for s in A]

    def rm(G, a, b):
        assert b in G[a]
        G[a].discard(b)
        G[b].discard(a)
    rm(M, z, w)
    for y, x in pairs:
        rm(M, z, y)
        rm(M, z, x)
        rm(M, y, x)
    K = [set(s) for s in M] + [set() for _ in range(k)]
    leaf = [n + i for i in range(k)]
    for i, (y, x) in enumerate(pairs):
        K[y].add(leaf[i])
        K[leaf[i]].add(y)
    Mplus = [set(s) for s in K]

    def live(G, i):
        return leaf[i] in G[pairs[i][0]]

    def Xset(G):
        X = set()
        for i in range(k):
            if live(G, i):
                X |= {leaf[i], pairs[i][1]}
        return X
    # replay
    levels = []
    for mv in mvs.split():
        levels.append(([set(s) for s in K], mv))
        ev = {v for v in range(len(K)) if even(K, v)}
        X = Xset(K)
        if mv[0] == 'M':
            a, b = map(int, mv[1:].split('-'))
            assert a in ev, (mv, 'not a token')
            assert b in K[a] and b not in ev and b not in X, (mv, 'bad target')
            rm(K, a, b)
            assert not (K[b] & (ev - {a})), (mv, 'target adjacent to another token')
        elif mv[0] == 'D':
            i = int(mv[1:])
            assert live(K, i) and len(K[pairs[i][0]]) % 2 == 1, (mv, 'bad drop')
            rm(K, pairs[i][0], leaf[i])
        elif mv[0] == 'S':
            pp, ab = mv[1:].split(':')
            pp = int(pp)
            a, b = map(int, ab.split('-'))
            assert pp in ev and K[pp] == {a, b} and a != b and b not in K[a], (mv, 'bad suppression')
            for i in range(k):
                assert a != leaf[i] and b != leaf[i], (mv, 'suppression at a leaf')
                if live(K, i):
                    assert {a, b} != {pairs[i][0], pairs[i][1]}, (mv, 'suppression creates x_i y_i')
            rm(K, pp, a)
            rm(K, pp, b)
            K[a].add(b)
            K[b].add(a)
        else:
            raise AssertionError('unknown move ' + mv)
    ev = [v for v in range(len(K)) if even(K, v)]
    nlive = sum(1 for i in range(k) if live(K, i))
    assert len(ev) <= 1 and nlive <= 1, ('bottom is not terminal', ev, nlive)
    lp = [(leaf[i], pairs[i][1]) for i in range(k) if live(K, i)]
    D = oracle_bottom(ora, K, lp)
    check_parity(K, D, lp, 'bottom')
    # undo
    for (Kprev, mv) in reversed(levels):
        if mv[0] == 'M':
            a, b = map(int, mv[1:].split('-'))
            en = ends_of(D)
            assert en.get(a, 0) == 1, (mv, 'b(p) != 1')
            assert all(en.get(v, 0) > 0 for v in K[b]), (mv, 'Z(u) nonempty')
            D = fan(D, a, b)
        elif mv[0] == 'D':
            i = int(mv[1:])
            D = D + [[leaf[i], pairs[i][0]]]
        else:
            pp, ab = mv[1:].split(':')
            pp = int(pp)
            a, b = map(int, ab.split('-'))
            hit = 0
            for j, P in enumerate(D):
                for t in range(len(P) - 1):
                    if {P[t], P[t + 1]} == {a, b}:
                        D[j] = P[:t + 1] + [pp] + P[t + 1:]
                        hit += 1
                        break
            assert hit == 1, (mv, 'edge ab not on exactly one path')
        K = Kprev
        lp = [(leaf[i], pairs[i][1]) for i in range(k) if live(K, i)]
        check_parity(K, D, lp, 'after undoing ' + mv)
    # top: M+, all tails live
    assert K == Mplus
    # delete the leaves
    D0 = []
    for P in D:
        Q = [v for v in P if v < n]
        assert len(Q) == len(P) or (len(Q) == len(P) - 1 and P[0] >= n or P[-1] >= n) or \
            (len(Q) == len(P) - 2 and P[0] >= n and P[-1] >= n), 'a leaf inside a path'
        if len(Q) >= 2:
            D0.append(Q)
    check_parity(M, D0, [], 'M')
    for y, x in pairs:
        Q = [P for P in D0 if P[0] == y or P[-1] == y]
        assert len(Q) == 1 and x not in Q[0], ('Q(y) meets x', y, x)
    # Test1 by the direct lift; tb.lift appends a_i b_i where Q(b_i) avoids a_i
    tbpairs = [(x, y) for (y, x) in pairs]
    paths = lift(J, z, r, tbpairs, D0)
    assert paths is not None, 'lift failed'
    verify_test1(J, z, r, paths)
    return len(mvs.split())


def main():
    ora = sys.argv[1]
    cnt = tot = 0
    for line in sys.stdin:
        if line.startswith('SCHED'):
            tot += check(ora, line.strip())
            cnt += 1
            if cnt % 500 == 0:
                print('progress', cnt, file=sys.stderr, flush=True)
    print('verified', cnt, 'schedules,', tot, 'moves in all')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""steer_verify.py: independent check of the two-token steering move (T2).
Reads SCHED lines of steer2.cpp (graph6, g, y, x, moves tok:p-q).  For each it executes the proof:
  1. G+ = G plus a leaf L at y;
  2. apply the moves (delete edge pq; the token moves to q) to get the bottom graph;
  3. find a decomposition of the bottom graph with b = degree parity (0 at even vertices) whose
     L-path avoids x (brute force; it exists by L1 / the leaf-tail lemma);
  4. undo the moves in reverse order, each by Fan's forced chain from p to q, checking Fan's
     hypothesis Z(q) = {} and b(p) = 1 at every step;
  5. delete the leaf and check that the result is a Lovasz decomposition of G with x not on Q(y).
It shares no code with the C++ tools (the decomposition enumerator and Fan chain are in brute.py,
whose decomposition search is also independent of dec.h)."""
import sys
sys.path.insert(0, '.')
from brute import parse_g6, decomps, fan

def check(line):
    p = line.split()
    G6, g, y, x = p[1], int(p[2]), int(p[3]), int(p[4])
    moves = [(int(m.split(':')[0]), int(m.split(':')[1].split('-')[0]), int(m.split('-')[1])) for m in p[5:]]
    n, adj = parse_g6(G6)
    L = n
    A = [set(a) for a in adj] + [set()]
    A[y].add(L); A[L].add(y)
    tok = {0: g, 1: y}
    levels = []   # graphs before each move
    for (t, a, b) in moves:
        assert tok[t] == a, (line, 'token position')
        assert b != x and b != L and b != tok[1 - t]
        levels.append(([set(s) for s in A], dict(tok)))
        A[a].discard(b); A[b].discard(a)
        # Z(b) must be empty in the graph after removal: b not adjacent to the other token
        o = tok[1 - t]
        assert o is None or o not in A[b], (line, 'adjacent to other token')
        tok[t] = b if A[b] else None
    # bottom: at most one even vertex
    ev = [v for v in range(n + 1) if A[v] and len(A[v]) % 2 == 0]
    assert len(ev) <= 1, (line, 'bottom has two even vertices')
    D = None
    for d in decomps(n + 1, A):
        P = [q for q in d if q[0] == L or q[-1] == L][0]
        if x not in P: D = [list(q) for q in d]; break
    assert D is not None, (line, 'bottom not solvable')
    # undo the moves
    for (t, a, b), (Aprev, tokprev) in zip(reversed(moves), reversed(levels)):
        # in the current graph, b(a) must be 1 and Z(b) empty
        ends = {}
        for q in D:
            for v in (q[0], q[-1]): ends[v] = ends.get(v, 0) + 1
        assert ends.get(a, 0) == 1, (line, 'b(t) != 1')
        assert all(ends.get(w, 0) > 0 for w in A[b]), (line, 'Z(w) nonempty')
        D, ch = fan(D, a, b)
        A[a].add(b); A[b].add(a)
        assert all(x not in q for q in D if L in q), (line, 'leaf path meets x')
    # top: G+ ; delete the leaf
    P = [q for q in D if q[0] == L or q[-1] == L][0]
    D.remove(P)
    if P[0] == L: P = P[1:]
    else: P = P[:-1]
    assert len(P) >= 2, (line, 'leaf path too short')
    D.append(P)
    # verify a Lovasz decomposition of G with x notin Q(y)
    used = set(); ends = {}
    for q in D:
        assert len(set(q)) == len(q)
        for i in range(len(q) - 1):
            e = frozenset((q[i], q[i + 1])); assert q[i + 1] in adj[q[i]] and e not in used; used.add(e)
        for v in (q[0], q[-1]): ends[v] = ends.get(v, 0) + 1
    assert len(used) == sum(len(a) for a in adj) // 2
    for v in range(n):
        assert ends.get(v, 0) == len(adj[v]) % 2, (line, 'not Lovasz')
    Q = [q for q in D if q[0] == y or q[-1] == y]
    assert len(Q) == 1 and x not in Q[0], (line, 'Q(y) meets x')
    return True

cnt = 0
for line in sys.stdin:
    if line.startswith('SCHED'):
        check(line); cnt += 1
print('verified', cnt, 'schedules')

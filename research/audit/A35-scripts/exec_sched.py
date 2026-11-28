#!/usr/bin/env python3
"""exec_sched.py (audit A35): independent replay and execution of two-token schedules.
Shares no code with the authors' scripts (own graph6 parser, own decomposition search, own Fan step).

Input: lines "SCHED g6 g y x t:p-q ..." (the output format of steer2.cpp with SCHED=1).
For each schedule:
  1. legality (Definition 6.3, literally): G+ = G + y l (l = n), X = {l, x}; each move t:p-q has the
     token t at p, pq an edge of the current graph, q not in X, q not the other token, q not adjacent
     to the other token after deleting pq; exactly the last move retires (q isolated after deletion);
  2. execution (proof of Theorem 6.5): a parity decomposition of the bottom graph whose l-path
     avoids x (exhaustive search); then the moves are undone in reverse order, each by Fan's forced
     chain from p to q, checking b(p) = 1 and Z(q) empty, the parity end counts, and "no path
     contains both l and x" after every step; finally l is deleted and the result is checked to be a
     Lovasz decomposition of G with x not on Q(y).
usage: python3 -I exec_sched.py [legal|exec] [every] < sched.txt
  legal: step 1 only; exec: steps 1 and 2; every k: execute only every k-th schedule (default 1)."""
import sys
sys.setrecursionlimit(10000)

def parse_g6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits.extend((v >> k) & 1 for k in range(5, -1, -1))
    adj = [set() for _ in range(n)]
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                adj[i].add(j); adj[j].add(i)
            p += 1
    return n, adj

def parity_decomp(edges, avoid_path=None):
    """edges: set of frozensets.  Returns a list of paths (vertex lists) with every vertex an end
    of exactly deg mod 2 paths, or None.  If avoid_path = (c, x): the path ending at c avoids x
    (c must be odd)."""
    memo = {}
    def deg(E):
        d = {}
        for e in E:
            for v in e: d[v] = d.get(v, 0) + 1
        return d
    def nbrs(E, v):
        return sorted(w for e in E if v in e for w in e if w != v)
    def solve(E, first=None):
        key = (E, first)
        if key in memo: return memo[key]
        if not E:
            memo[key] = []; return []
        d = deg(E)
        if first is None:
            odd = sorted(v for v in d if d[v] % 2)
            if not odd:
                memo[key] = None; return None
            w, banned = odd[0], None
        else:
            w, banned = first
        res = None
        def grow(path, rem):
            c = path[-1]
            for z in nbrs(rem, c):
                if z in path or z == banned: continue
                e = frozenset((c, z)); r2 = rem - {e}; p2 = path + [z]
                if d[z] % 2:
                    sub = solve(r2)
                    if sub is not None: return [p2] + sub
                out = grow(p2, r2)
                if out is not None: return out
            return None
        res = grow([w], E)
        memo[key] = res
        return res
    E = frozenset(edges)
    if avoid_path is None: return solve(E)
    return solve(E, avoid_path)

def ends_count(D):
    b = {}
    for P in D:
        for v in (P[0], P[-1]): b[v] = b.get(v, 0) + 1
    return b

def check_parity(D, edges, verts):
    used = set()
    for P in D:
        assert len(P) >= 2 and len(set(P)) == len(P), ('not a path', P)
        for a, c in zip(P, P[1:]):
            e = frozenset((a, c)); assert e in edges and e not in used, ('edge', P); used.add(e)
    assert used == edges, 'not a decomposition'
    deg = {v: 0 for v in verts}
    for e in edges:
        for v in e: deg[v] += 1
    b = ends_count(D)
    for v in verts: assert b.get(v, 0) == deg[v] % 2, ('ends', v)

def fan_step(D, t, w):
    """Fan's forced chain from t to the new edge tw (Section 2), sequential re-routing.
    D: decomposition of H' (t, w non-adjacent), b <= 1 everywhere.  Returns the decomposition of
    H' + tw."""
    D = [list(P) for P in D]
    xj, last = t, None
    while True:
        idx = [i for i, P in enumerate(D) if (P[0] == xj or P[-1] == xj) and i != last]
        assert len(idx) == 1, ('end at chain vertex not unique', xj)
        i = idx[0]; P = D[i]
        if P[-1] == xj: P = P[::-1]
        if w not in P:
            D[i] = [w] + P          # append w at the end x_k
            return D
        k = P.index(w)
        s = P[k - 1]                # sigma(x_j): the vertex before w read from x_j
        assert k >= 2, 'sigma(x_j) = x_j'
        # P = x_j W s w W'  ->  s W^{-1} x_j w W'
        D[i] = P[:k][::-1] + P[k:]
        last, xj = i, s

def run(line, do_exec):
    p = line.split()
    g6, g, y, x = p[1], int(p[2]), int(p[3]), int(p[4])
    moves = []
    for mv in p[5:]:
        t, r = mv.split(':'); a, c = r.split('-'); moves.append((int(t), int(a), int(c)))
    n, adj = parse_g6(g6)
    L = n
    edges = {frozenset((a, c)) for a in range(n) for c in adj[a]} | {frozenset((y, L))}
    verts = list(range(n + 1))
    X = {L, x}
    tok = [g, y]
    cur = set(edges)
    levels = []
    for i, (t, a, q) in enumerate(moves):
        o = tok[1 - t]
        assert tok[t] == a, 'token position'
        e = frozenset((a, q))
        assert e in cur, 'edge'
        assert q not in X and q != o, 'target'
        levels.append(set(cur))
        cur.discard(e)
        assert frozenset((q, o)) not in cur, 'adjacent to the other token'
        iso = not any(q in f for f in cur)
        assert iso == (i == len(moves) - 1), 'retirement only at the last move'
        tok[t] = q
    if not do_exec: return
    deg = {v: 0 for v in verts}
    for e in cur:
        for v in e: deg[v] += 1
    assert sum(1 for v in verts if deg[v] > 0 and deg[v] % 2 == 0) <= 1, 'bottom has two even vertices'
    D = parity_decomp(cur, (L, x))
    assert D is not None, 'bottom not solvable'
    check_parity(D, cur, verts)
    def meets_once(D):
        return all(not (L in P and x in P) for P in D)
    assert meets_once(D)
    for (t, a, q), prev in zip(reversed(moves), reversed(levels)):
        b = ends_count(D)
        assert b.get(a, 0) == 1, 'b(t) != 1'
        nb = [w for f in cur if q in f for w in f if w != q]
        assert all(b.get(w, 0) >= 1 for w in nb), 'Z(w) not empty'
        D = fan_step(D, a, q)
        cur = prev
        check_parity(D, cur, verts)
        assert meets_once(D), 'meets X twice'
    assert cur == edges
    P = [P for P in D if L in P][0]
    D.remove(P)
    if P[-1] == L: P = P[::-1]
    assert P[0] == L and len(P) >= 3
    D.append(P[1:])
    Gedges = edges - {frozenset((y, L))}
    check_parity(D, Gedges, list(range(n)))
    Q = [P for P in D if P[0] == y or P[-1] == y]
    assert len(Q) == 1 and x not in Q[0], 'Q(y) meets x'

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'exec'
    every = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    cnt = ex = 0
    for line in sys.stdin:
        if not line.startswith('SCHED'): continue
        do_exec = mode == 'exec' and cnt % every == 0
        run(line, do_exec)
        cnt += 1; ex += do_exec
    print(f'{cnt} schedules legal; {ex} executed and verified')

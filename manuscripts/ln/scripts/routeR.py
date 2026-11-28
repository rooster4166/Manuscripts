"""routeR.py -- Criterion R for L_N(2), with an independent executor (ln session).

Criterion R: for some i in {1, 2} (j the other index) there is a path P starting at c_i and avoiding
a_i such that, with K = F - E(P), and
  * if P ends at c_j and avoids a_j: no tail;
  * otherwise (P must not end at a_j, so that a_j stays odd) a tail for c_j: c_j itself if it is a
    leaf of K at distance >= 3 from a_j, else a new leaf l at c_j (K := K + c_j l, tail (l, c_j, a_j)),
the graph K has a token schedule (moves M, D, S of the multi-token calculus) ending with at most one
token and at most one live tail.  Then L_N(2) holds: execute the schedule backwards (Fan's forced
chain for M, the path cs for D, subdivision for S) from a bottom decomposition, delete the leaf,
and add P, which becomes Q(c_i) (and Q(c_j) in the joint case).

For every instance on stdin ('g6 c1 a1 c2 a2') the search finds a certificate (i, P, moves), the
executor rebuilds the decomposition from scratch (the bottom by lnsolve, checked) and verifies the
final Lovasz decomposition of F with a_1 not on Q(c_1) and a_2 not on Q(c_2) by lnlib.check_witness.
usage: routeR.py LNSOLVE < instances    (prints one line per instance; summary on stderr)
"""
import sys, subprocess
from lnlib import g6_decode, g6_encode, check_witness

def ekey(a, b): return (a, b) if a < b else (b, a)

def search(N, E, tails):
    """token schedule; returns the list of moves or None"""
    seen = set()
    def rec(E, tails):
        key = (E, tails)
        if key in seen: return None
        seen.add(key)
        d = [0] * N; A = [set() for _ in range(N)]
        for u, v in E: d[u] += 1; d[v] += 1; A[u].add(v); A[v].add(u)
        tok = [v for v in range(N) if d[v] > 0 and d[v] % 2 == 0]
        if len(tok) <= 1 and len(tails) <= 1: return []
        ts = set(tok); X = set()
        for (c, s, x) in tails: X |= {c, x}
        for p in tok:
            for u in sorted(A[p]):
                if d[u] % 2 == 0 or u in X: continue
                if any(w in ts and w != p for w in A[u] if w != p): continue
                r = rec(E - {ekey(p, u)}, tails)
                if r is not None: return [('M', p, u)] + r
        for i, (c, s, x) in enumerate(tails):
            if d[s] % 2 == 1:
                r = rec(E - {ekey(c, s)}, tails[:i] + tails[i + 1:])
                if r is not None: return [('D', c, s)] + r
        leaves = {c for (c, s, x) in tails}
        for p in tok:
            if d[p] != 2 or p in X: continue
            a, b = sorted(A[p])
            if b in A[a] or a in leaves or b in leaves: continue
            if any({a, b} == {x, s} for (c, s, x) in tails): continue
            r = rec(frozenset((E - {ekey(p, a), ekey(p, b)}) | {ekey(a, b)}), tails)
            if r is not None: return [('S', p, a, b)] + r
        return None
    return rec(frozenset(E), tuple(tails))

def find(n, adj, c1, a1, c2, a2, maxlen=None):
    E0 = set(ekey(u, v) for u in range(n) for v in adj[u])
    for (ci, ai, cj, aj) in ((c1, a1, c2, a2), (c2, a2, c1, a1)):
        paths = []
        def ext(P, S):
            if len(P) >= 2: paths.append(list(P))
            if P[-1] == cj and len(P) >= 2: return
            if maxlen and len(P) > maxlen: return
            for y in sorted(adj[P[-1]]):
                if y not in S and y != ai:
                    S.add(y); P.append(y); ext(P, S); P.pop(); S.discard(y)
        ext([ci], {ci})
        paths.sort(key=len)
        for P in paths:
            E = E0 - set(ekey(p, q) for p, q in zip(P, P[1:]))
            N = n
            if P[-1] == cj:
                if aj in P: continue
                tails = []
            else:
                if P[-1] == aj: continue   # keep the head a_j odd (invariant (TI) of multi-token)
                A = [set() for _ in range(n)]
                for u, v in E: A[u].add(v); A[v].add(u)
                if len(A[cj]) == 0: continue
                w = next(iter(A[cj])) if len(A[cj]) == 1 else None
                if w is not None and aj != w and aj not in A[w]:
                    tails = [(cj, w, aj)]
                else:
                    E = E | {(cj, n)}; tails = [(n, cj, aj)]; N = n + 1
            mv = search(N, E, tails)
            if mv is not None:
                return (ci, ai, cj, aj, P, N, E, tails, mv)
    return None

def fan(D, t, w):
    """Fan's forced chain (cf. multi-token mt_verify.py): add the edge tw to the parity
    decomposition D of the current graph; t has one end, w none, every neighbour of w one end."""
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
        if P[-1] == x: P = P[::-1]
        if w not in P:
            D[i] = [w] + P
            return D
        k = P.index(w)
        D[i] = P[:k][::-1] + P[k:]
        x = P[k - 1]

def adj_of(N, E):
    A = [set() for _ in range(N)]
    for u, v in E: A[u].add(v); A[v].add(u)
    return A

def check_level(N, E, D, tails, where):
    A = adj_of(N, E)
    req = [len(A[v]) % 2 for v in range(N)]
    sep = [(c, x) for (c, s, x) in tails if ekey(c, s) in E]
    err = check_witness(N, A, req, [], sep, D)
    assert err is None, (where, err)

def execute(solver, n, adj, cert):
    ci, ai, cj, aj, P, N, E, tails, mv = cert
    levels = [(frozenset(E), tuple(tails))]
    curE, curT = frozenset(E), tuple(tails)
    for m in mv:
        if m[0] == 'M':
            curE = curE - {ekey(m[1], m[2])}
        elif m[0] == 'D':
            curE = curE - {ekey(m[1], m[2])}
            curT = tuple(t for t in curT if not (t[0] == m[1] and t[1] == m[2]))
        else:
            _, p, a, b = m
            curE = frozenset((curE - {ekey(p, a), ekey(p, b)}) | {ekey(a, b)})
        levels.append((curE, curT))
    # bottom: exact solve with the live tail constraints
    A = adj_of(N, curE)
    deg = [len(a) for a in A]
    assert sum(1 for v in range(N) if deg[v] > 0 and deg[v] % 2 == 0) <= 1
    live = [(c, x) for (c, s, x) in curT if ekey(c, s) in curE]
    assert len(live) <= 1
    q = g6_encode(N, A) + ''.join(' S %d %d' % lx for lx in live)
    out = subprocess.run([solver], input=q + '\n', capture_output=True, text=True).stdout.strip()
    assert out.startswith('SAT'), ('bottom', out)
    D = [list(map(int, s.split('-'))) for s in out.split('::', 1)[1].split(';') if s.strip()]
    check_level(N, curE, D, curT, 'bottom')
    for k in range(len(mv) - 1, -1, -1):
        m = mv[k]; E_up, T_up = levels[k]
        if m[0] == 'M':
            _, p, u = m
            D = fan(D, p, u)
        elif m[0] == 'D':
            D = D + [[m[1], m[2]]]
        else:
            _, p, a, b = m
            D2 = []
            for Q in D:
                for r in range(len(Q) - 1):
                    if {Q[r], Q[r + 1]} == {a, b}:
                        Q = Q[:r + 1] + [p] + Q[r + 1:]
                        break
                D2.append(Q)
            D = D2
        check_level(N, E_up, D, T_up, 'level %d' % k)
    # delete the new leaf (if any) and add P
    if N == n + 1:
        D = [[v for v in Q if v != n] for Q in D]
        D = [Q for Q in D if len(Q) >= 2]
    D = D + [list(P)]
    req = [len(adj[v]) % 2 for v in range(n)]
    err = check_witness(n, adj, req, [(c1g, a1g), (c2g, a2g)], [], D)
    assert err is None, ('final', err)
    return D

if __name__ == '__main__':
    solver = sys.argv[1]
    tot = ok = 0; kinds = {}
    for line in sys.stdin:
        t = line.split()
        if not t: continue
        g = t[0]; n, adj = g6_decode(g); c1g, a1g, c2g, a2g = map(int, t[1:5])
        tot += 1
        cert = find(n, adj, c1g, a1g, c2g, a2g)
        if cert is None:
            print('NOCERT', line.strip(), flush=True); continue
        try:
            execute(solver, n, adj, cert)
            kind = 'joint' if cert[4][-1] == cert[2] else 'pre'
            kinds[kind] = kinds.get(kind, 0) + 1
            ok += 1
            print('OK', kind, line.strip(), 'P=' + '-'.join(map(str, cert[4])), 'moves=%d' % len(cert[8]), flush=True)
        except AssertionError as e:
            print('EXECFAIL', line.strip(), repr(e)[:200], flush=True)
    print('total', tot, 'certified and executed', ok, kinds, file=sys.stderr)

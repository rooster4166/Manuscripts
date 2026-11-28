"""r3.py -- Criterion R3 for L_N(3): pre-commit end paths, then a multi-token schedule with one
tail for the remaining pair.  For an instance (F; (c_t, a_t), t = 1, 2, 3) we try, over the
orderings (i, j, k):
  A  joint: P from c_i to c_j avoiding a_i, a_j (a_k not an end); remaining pair k as a tail;
  B  two paths: P1 from c_i avoiding a_i, P2 from c_j avoiding a_j, edge-disjoint, the four ends
     distinct and outside {c_k, a_k}; remaining pair k as a tail (paths of length <= LMAX).
The tail is the leaf variant (c_k, w, a_k) if c_k is a leaf of K0 at w with a_k outside N[w], else a
new leaf.  Every certificate is executed: the moves are replayed, the bottom is solved exactly,
the moves are undone (Fan's forced chain, the path cs, subdivision), every level is checked, the
leaf is deleted, the paths are added, and the final Lovasz decomposition of F is checked with all
three avoidances.  usage: r3.py LNSOLVE LMAX < 'g6 A c1 a1 A c2 a2 A c3 a3' lines"""
import sys, itertools, subprocess
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode, g6_encode, check_witness
from routeR import search, ekey, fan, adj_of, check_level

def paths_from(adj, s, avoid, maxlen, stop=None):
    out = []
    def ext(P, S):
        if len(P) >= 2: out.append(tuple(P))
        if len(P) - 1 >= maxlen: return
        if stop is not None and P[-1] == stop and len(P) >= 2: return
        for y in sorted(adj[P[-1]]):
            if y not in S and y not in avoid:
                S.add(y); P.append(y); ext(P, S); P.pop(); S.discard(y)
    ext([s], {s})
    out.sort(key=len)
    return out

def tail_for(n, E, ck, ak):
    A = adj_of(n, E)
    if len(A[ck]) == 0: return None
    if len(A[ck]) == 1:
        w = next(iter(A[ck]))
        if ak != w and ak not in A[w]: return n, E, [(ck, w, ak)]
    return n + 1, E | {(ck, n)}, [(n, ck, ak)]

def candidates(n, adj, T, LMAX):
    E0 = frozenset(ekey(u, v) for u in range(n) for v in adj[u])
    for (i, j, k) in itertools.permutations(range(3)):
        (ci, ai), (cj, aj), (ck, ak) = T[i], T[j], T[k]
        if i < j:   # A: joint
            for P in paths_from(adj, ci, {ai, aj}, n, stop=cj):
                if P[-1] != cj: continue
                E = E0 - set(ekey(p, q) for p, q in zip(P, P[1:]))
                yield ('A', (i, j, k), [P], E)
    for (i, j, k) in itertools.permutations(range(3)):
        if i > j: continue
        (ci, ai), (cj, aj), (ck, ak) = T[i], T[j], T[k]
        for P1 in paths_from(adj, ci, {ai}, LMAX):
            E1 = E0 - set(ekey(p, q) for p, q in zip(P1, P1[1:]))
            adj1 = adj_of(n, E1)
            for P2 in paths_from(adj1, cj, {aj}, LMAX):
                ends = [P1[0], P1[-1], P2[0], P2[-1]]
                if len(set(ends)) < 4 or ck in ends or ak in ends: continue
                E = E1 - set(ekey(p, q) for p, q in zip(P2, P2[1:]))
                yield ('B', (i, j, k), [P1, P2], E)

def execute(solver, n, adj, T, cert):
    kind, (i, j, k), Ps, N, E, tails, mv = cert
    levels = [(frozenset(E), tuple(tails))]
    curE, curT = frozenset(E), tuple(tails)
    for m in mv:
        if m[0] == 'M': curE = curE - {ekey(m[1], m[2])}
        elif m[0] == 'D':
            curE = curE - {ekey(m[1], m[2])}
            curT = tuple(t for t in curT if not (t[0] == m[1] and t[1] == m[2]))
        else:
            _, p, a, b = m
            curE = frozenset((curE - {ekey(p, a), ekey(p, b)}) | {ekey(a, b)})
        levels.append((curE, curT))
    A = adj_of(N, curE)
    live = [(c, x) for (c, s, x) in curT if ekey(c, s) in curE]
    q = g6_encode(N, A) + ''.join(' S %d %d' % lx for lx in live)
    out = subprocess.run([solver], input=q + '\n', capture_output=True, text=True).stdout.strip()
    assert out.startswith('SAT'), ('bottom', out)
    D = [list(map(int, s.split('-'))) for s in out.split('::', 1)[1].split(';') if s.strip()]
    check_level(N, curE, D, curT, 'bottom')
    for t in range(len(mv) - 1, -1, -1):
        m = mv[t]; E_up, T_up = levels[t]
        if m[0] == 'M': D = fan(D, m[1], m[2])
        elif m[0] == 'D': D = D + [[m[1], m[2]]]
        else:
            _, p, a, b = m
            D2 = []
            for Q in D:
                for r in range(len(Q) - 1):
                    if {Q[r], Q[r + 1]} == {a, b}:
                        Q = Q[:r + 1] + [p] + Q[r + 1:]; break
                D2.append(Q)
            D = D2
        check_level(N, E_up, D, T_up, 'level %d' % t)
    if N == n + 1:
        D = [[v for v in Q if v != n] for Q in D]
        D = [Q for Q in D if len(Q) >= 2]
    D = D + [list(P) for P in Ps]
    req = [len(adj[v]) % 2 for v in range(n)]
    err = check_witness(n, adj, req, list(T), [], D)
    assert err is None, ('final', err)

def find(n, adj, T, LMAX):
    for kind, (i, j, k), Ps, E in candidates(n, adj, T, LMAX):
        ck, ak = T[k]
        tf = tail_for(n, E, ck, ak)
        if tf is None: continue
        N, EK, tails = tf
        mv = search(N, EK, tails)
        if mv is not None: return (kind, (i, j, k), Ps, N, EK, tails, mv)
    return None

if __name__ == '__main__':
    solver = sys.argv[1]; LMAX = int(sys.argv[2])
    tot = ok = 0; kinds = {}
    for line in sys.stdin:
        t = line.split()
        if not t: continue
        n, adj = g6_decode(t[0])
        nums = [int(x) for x in t[1:] if x != 'A']
        T = [(nums[0], nums[1]), (nums[2], nums[3]), (nums[4], nums[5])]
        tot += 1
        cert = find(n, adj, T, LMAX)
        if cert is None:
            print('NOCERT', line.strip(), flush=True); continue
        try:
            execute(solver, n, adj, T, cert)
            ok += 1; kinds[cert[0]] = kinds.get(cert[0], 0) + 1
            print('OK', cert[0], line.strip(), 'P=' + ' '.join('-'.join(map(str, P)) for P in cert[2]),
                  'moves=%d' % len(cert[6]), flush=True)
        except AssertionError as e:
            print('EXECFAIL', line.strip(), repr(e)[:200], flush=True)
    print('total', tot, 'certified and executed', ok, kinds, file=sys.stderr)

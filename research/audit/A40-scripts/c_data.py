"""c_data.py -- (c) independent re-verification of Criterion R certificates.

usage: python3 c_data.py DATAFILE COUNT SEED [all]
For a random sample of COUNT lines 'OK kind g6 c1 a1 c2 a2 P=.. moves=k' of DATAFILE:
 1. checks the instance (connected, all degrees odd, pairs disjoint, c_i !~ a_i) with own code;
 2. decides the instance with the audit's solver trsolve ('A c1 a1 A c2 a2') and checks the witness;
 3. recovers the certificate with routeR.find (search only) and checks that P and the number of
    moves agree with the data line;
 4. checks the certificate against the definitions of multi-token Def. 2.1/2.2 with own code:
    P a path of F from c_i avoiding a_i; joint case: P ends at c_j and avoids a_j, no tail;
    otherwise P does not end at a_j and the tail is (c_j, w, a_j) or (l, c_j, a_j); (TS) and (TI)
    at the start; every move legal (M: u odd, u not in X, no other token next to u; D: stem odd;
    S: deg p = 2, a !~ b, a, b not leaves, {a,b} != {x,s}); at the end <= 1 token, <= 1 live tail;
    (TI) re-checked after every move;
 5. executes the certificate with own code: the bottom by trsolve (S c x for the live tail),
    then each move undone (own Fan chain, drop path, subdivision), every level checked with
    a40lib.check, the leaf deleted, P added, and the final Lovasz decomposition checked.
"""
import sys, os, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, '..', '..', '..', 'manuscripts', 'ln', 'scripts'))
from a40lib import dec, enc, check, solve_lines
import routeR   # used only for routeR.find (the search)


def ek(a, b):
    return (a, b) if a < b else (b, a)


def adjof(N, E):
    A = [set() for _ in range(N)]
    for u, v in E:
        A[u].add(v); A[v].add(u)
    return A


def connected(n, A):
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in A[x]:
            if y not in seen:
                seen.add(y); st.append(y)
    return len(seen) == n


def tokens(N, A):
    return {v for v in range(N) if A[v] and len(A[v]) % 2 == 0}


def check_TI(N, E, tails):
    A = adjof(N, E)
    for (c, s, x) in tails:
        if ek(c, s) not in E:
            continue  # not live
        assert A[c] == {s}, 'TI: N(c) != {s}'
        assert len(A[x]) % 2 == 1, 'TI: x not odd'
        assert x not in A[s], 'TI: x ~ s'


def legal(n, F, c1, a1, c2, a2, cert):
    ci, ai, cj, aj, P, N, E, tails, mv = cert
    assert {ci, cj} == {c1, c2} and {(ci, ai), (cj, aj)} == {(c1, a1), (c2, a2)}
    assert P[0] == ci and len(P) >= 2 and len(set(P)) == len(P) and ai not in P
    for x, y in zip(P, P[1:]):
        assert y in F[x]
    EF = {ek(u, v) for u in range(n) for v in F[u]}
    E0 = EF - {ek(x, y) for x, y in zip(P, P[1:])}
    if P[-1] == cj:
        assert aj not in P and tails == [] and N == n and set(E) == E0, 'joint case'
    else:
        assert P[-1] != aj, 'P ends at a_j'
        A0 = adjof(n, E0)
        if len(A0[cj]) == 1 and N == n:
            (w,) = A0[cj]
            assert tails == [(cj, w, aj)] and set(E) == E0
        else:
            assert N == n + 1 and tails == [(n, cj, aj)] and set(E) == E0 | {(cj, n)}
        for (c, s, x) in tails:   # (TS) for a single tail
            assert x not in (c, s)
    E = frozenset(E); T = list(tails)
    check_TI(N, E, T)
    for m in mv:
        A = adjof(N, E); tok = tokens(N, A)
        live = [t for t in T if ek(t[0], t[1]) in E]
        X = set()
        for (c, s, x) in live:
            X |= {c, x}
        if m[0] == 'M':
            _, p, u = m
            assert p in tok and u in A[p] and len(A[u]) % 2 == 1 and u not in X
            assert not any(w in tok for w in A[u] - {p}), 'M: other token next to u'
            E = E - {ek(p, u)}
        elif m[0] == 'D':
            _, c, s = m
            assert any(t[0] == c and t[1] == s for t in live) and len(A[s]) % 2 == 1
            E = E - {ek(c, s)}
            T = [t for t in T if not (t[0] == c and t[1] == s)]
        else:
            _, p, a, b = m
            assert p in tok and A[p] == {a, b} and b not in A[a]
            assert all(a != t[0] and b != t[0] for t in T)
            assert all({a, b} != {t[2], t[1]} for t in live)
            E = frozenset((E - {ek(p, a), ek(p, b)}) | {ek(a, b)})
        check_TI(N, E, T)
    A = adjof(N, E)
    assert len(tokens(N, A)) <= 1, 'more than one token at the end'
    assert len([t for t in T if ek(t[0], t[1]) in E]) <= 1


def fan_chain(D, p, u):
    """own implementation of Fan's forced chain: add the edge pu.  Pre: p has one end, u none,
    every neighbour of u one end.  Each step: take a path ending at the current vertex x that
    was not created in the previous step; if u is not on it, attach u; otherwise rotate at the
    predecessor y of u, freeing yu, and continue at y."""
    D = [list(Q) for Q in D]
    x, last = p, None
    for _ in range(10 * sum(len(Q) for Q in D) + 10):
        cand = [i for i, Q in enumerate(D) if x in (Q[0], Q[-1]) and i != last]
        assert len(cand) == 1, ('fan: ends at', x, cand)
        i = cand[0]
        Q = D[i] if D[i][0] == x else D[i][::-1]
        if u not in Q:
            D[i] = [u] + Q
            return D
        k = Q.index(u)
        y = Q[k - 1]
        # Q = x .. y u ..  ->  y .. x u ..  (edge xu added, edge yu freed)
        D[i] = Q[:k][::-1] + Q[k:]
        x, last = y, i
    raise AssertionError('fan: no termination')


def execute(n, F, c1, a1, c2, a2, cert):
    ci, ai, cj, aj, P, N, E, tails, mv = cert
    levels = [(frozenset(E), list(tails))]
    E = frozenset(E); T = list(tails)
    for m in mv:
        if m[0] == 'M':
            E = E - {ek(m[1], m[2])}
        elif m[0] == 'D':
            E = E - {ek(m[1], m[2])}
            T = [t for t in T if not (t[0] == m[1] and t[1] == m[2])]
        else:
            _, p, a, b = m
            E = frozenset((E - {ek(p, a), ek(p, b)}) | {ek(a, b)})
        levels.append((E, list(T)))

    def lvl_check(E, T, D, where):
        A = adjof(N, E)
        sep = [(c, x) for (c, s, x) in T if ek(c, s) in E]
        err = check(N, A, D, None, (), sep)
        assert err is None, (where, err)

    A = adjof(N, E)
    sep = [(c, x) for (c, s, x) in T if ek(c, s) in E]
    (ans, D), = solve_lines([enc(N, A) + ''.join(' S %d %d' % q for q in sep)])
    assert ans == 'SAT', ('bottom', ans)
    lvl_check(E, T, D, 'bottom')
    for k in range(len(mv) - 1, -1, -1):
        m = mv[k]
        Eu, Tu = levels[k]
        if m[0] == 'M':
            D = fan_chain(D, m[1], m[2])
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
        lvl_check(Eu, Tu, D, 'level %d' % k)
    if N == n + 1:
        D = [[v for v in Q if v != n] for Q in D]
        D = [Q for Q in D if len(Q) >= 2]
    D = D + [list(P)]
    err = check(n, F, D, [1] * n, [(c1, a1), (c2, a2)])
    assert err is None, ('final', err)


if __name__ == '__main__':
    path, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    lines = [l.split() for l in open(path) if l.strip()]
    bad = [l for l in lines if l[0] != 'OK']
    rng = random.Random(seed)
    sample = lines if (len(sys.argv) > 4 and sys.argv[4] == 'all') else rng.sample(lines, min(count, len(lines)))
    # 2. satisfiability by trsolve, in one batch
    qs = ['%s A %s %s A %s %s' % (t[2], t[3], t[4], t[5], t[6]) for t in sample]
    sat = solve_lines(qs, budget=2000000000)
    stat = {'lines': len(lines), 'non-OK lines': len(bad), 'sampled': len(sample), 'inst_ok': 0,
            'trsolve_SAT': 0, 'cert_match': 0, 'legal': 0, 'executed': 0}
    kinds = {}
    for t, (ans, W) in zip(sample, sat):
        g = t[2]; c1, a1, c2, a2 = map(int, t[3:7])
        n, F = dec(g)
        try:
            assert connected(n, F) and all(len(a) % 2 == 1 for a in F)
            assert len({c1, a1, c2, a2}) == 4 and a1 not in F[c1] and a2 not in F[c2]
            stat['inst_ok'] += 1
            assert ans == 'SAT', 'trsolve ' + ans
            assert check(n, F, W, [1] * n, [(c1, a1), (c2, a2)]) is None, 'trsolve witness'
            stat['trsolve_SAT'] += 1
            cert = routeR.find(n, F, c1, a1, c2, a2)
            Pd = [x for x in t if x.startswith('P=')][0][2:]
            md = int([x for x in t if x.startswith('moves=')][0][6:])
            assert cert is not None and '-'.join(map(str, cert[4])) == Pd and len(cert[8]) == md, 'cert mismatch'
            kind = 'joint' if cert[4][-1] == cert[2] else 'pre'
            assert kind == t[1]
            stat['cert_match'] += 1
            legal(n, F, c1, a1, c2, a2, cert)
            stat['legal'] += 1
            execute(n, F, c1, a1, c2, a2, cert)
            stat['executed'] += 1
            leafvar = cert[5] == n and kind == 'pre'
            key = (kind, 'leafvariant' if leafvar else ('newleaf' if kind == 'pre' else '-'),
                   'S' if any(m[0] == 'S' for m in cert[8]) else '', 'D' if any(m[0] == 'D' for m in cert[8]) else '')
            kinds[key] = kinds.get(key, 0) + 1
        except AssertionError as e:
            print('FAIL', ' '.join(t), repr(e)[:300], flush=True)
    print(stat)
    print('certificate shapes (route, tail, uses S, uses D):', kinds)

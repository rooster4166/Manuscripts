"""Audit A22c: the far-apart form (Prop 8.3, Cor 8.4) and the d6_reach table, with an own random
generator (configuration model, multi-edges and loops rejected, own 3-connectivity test).
For J with N(z) pairwise at distance >= 3 in J - z: for every r, look for a labelled pairing with
r = some y_i and an admissible chain, in three ways:
  strict-greedy : Definition 8.1 / Lean AdmChain (N(.) in G), P2 a BFS-shortest constrained path,
                  then P1 a BFS-shortest constrained path edge-disjoint from P2 (as d6_reach.py);
  relaxed-greedy: the same with N(.) in G - F (what d6_reach.py implements: y3 may lie on P1);
  strict-any    : strict, trying all P2 of length <= shortest + 2 before giving up.
Optionally (verify=K) for the first K far graphs of order <= 61: build M for one chain per covered
r, check the sparse/packed hypotheses of Theorem 3.2 directly, find the separating decomposition
by dsolve, and execute the proof of Theorem 8.2 (construct.py) to the final decomposition of G.
usage: far_check.py COUNT SEED n1 n2 ... [verify=K]"""
import sys, random, itertools
from collections import deque
from chain import FLAGS, configs, rules, bfs_len, paths, pedges, base_test
import construct


def rand_J(n, rng):
    while True:
        degs = [6] + [rng.choice((3, 3, 3, 5)) for _ in range(n - 1)]
        if sum(degs) % 2:
            continue
        stubs = [v for v in range(n) for _ in range(degs[v])]
        rng.shuffle(stubs)
        E = set(); ok = True
        for i in range(0, len(stubs), 2):
            a, b = stubs[i], stubs[i + 1]
            e = frozenset((a, b))
            if a == b or e in E:
                ok = False; break
            E.add(e)
        if not ok:
            continue
        adj = [set() for _ in range(n)]
        for e in E:
            a, b = tuple(e); adj[a].add(b); adj[b].add(a)
        if three_conn(n, adj):
            return adj


def conn(n, adj, gone):
    s = next(v for v in range(n) if v not in gone)
    seen = {s}; st = [s]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in gone and y not in seen:
                seen.add(y); st.append(y)
    return len(seen) == n - len(gone)


def three_conn(n, adj):
    if not conn(n, adj, set()):
        return False
    for u in range(n):
        if not conn(n, adj, {u}):
            return False
    for u, v in itertools.combinations(range(n), 2):
        if not conn(n, adj, {u, v}):
            return False
    return True


def bfs_path(adj, s, t, inner, banned=frozenset()):
    prev = {s: None}; q = deque([s])
    while q:
        v = q.popleft()
        if v == t:
            p = [t]
            while prev[p[-1]] is not None:
                p.append(prev[p[-1]])
            return p[::-1]
        for w in sorted(adj[v]):
            if w in prev or frozenset((v, w)) in banned:
                continue
            if w != t and not inner(w):
                continue
            prev[w] = v; q.append(w)
    return None


def pairings(xs):
    if not xs:
        yield []
        return
    for i in range(1, len(xs)):
        for p in pairings(xs[1:i] + xs[i + 1:]):
            yield [(xs[0], xs[i])] + p


def find_chain(n, E, X, Y, fl, how):
    GF, pre, inner2, inner1 = rules(n, E, X, Y, fl)
    if not pre:
        return None
    if how == 'greedy':
        P2 = bfs_path(GF, Y[2], X[1], inner2)
        if P2 is None:
            return None
        P1 = bfs_path(GF, Y[1], X[0], inner1, pedges(P2))
        return (P2, P1) if P1 else None
    d2 = bfs_len(GF, Y[2], X[1], inner2)
    if d2 is None:
        return None
    for P2 in paths(GF, Y[2], X[1], inner2, d2 + 2):
        P1 = bfs_path(GF, Y[1], X[0], inner1, pedges(P2))
        if P1:
            return P2, P1
    return None


def main():
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    verify = 0
    orders = []
    for a in sys.argv[3:]:
        if a.startswith('verify='):
            verify = int(a.split('=')[1])
        else:
            orders.append(int(a))
    rng = random.Random(seed)
    strict = dict(FLAGS); relaxed = dict(FLAGS, nbrH=True)
    for n in orders:
        far = cov = {'sg': 0, 'rg': 0, 'sa': 0}
        far = 0; cov = dict(sg=0, rg=0, sa=0); y3_on_P1 = 0; verified = 0
        for _ in range(count):
            adj = rand_J(n, rng)
            Nz = sorted(adj[0])
            H = [set(a) - {0} for a in adj]
            def d2(u, v):
                return v in H[u] or bool(H[u] & H[v])
            if any(d2(u, v) for u, v in itertools.combinations(Nz, 2)):
                continue
            far += 1
            # G = (J - z) + F on vertices 1..n-1 relabelled 0..n-2
            lab = {v: i for i, v in enumerate(range(1, n))}
            E0 = {frozenset((lab[a], lab[b])) for a in range(1, n) for b in H[a] if a < b}
            N6 = [lab[v] for v in Nz]
            got = dict(sg=set(), rg=set(), sa=set()); wit = {}
            for F in pairings(N6):
                E = E0 | {frozenset(p) for p in F}
                for X, Y in configs(F):
                    for key, fl, how in (('sg', strict, 'greedy'), ('rg', relaxed, 'greedy'), ('sa', strict, 'any')):
                        if set(Y) <= got[key]:
                            continue
                        c = find_chain(n - 1, E, X, Y, fl, how)
                        if c:
                            got[key] |= set(Y)
                            if key == 'rg' and Y[2] in c[1]:
                                y3_on_P1 += 1
                            if key == 'sa':
                                for y in Y:
                                    wit.setdefault(y, (E, X, Y, c))
                if all(len(g) == 6 for g in got.values()):
                    break
            for k in cov:
                cov[k] += len(got[k]) == 6
            if verified < verify and n <= 61:
                verified += 1
                for y, (E, X, Y, (P2, P1)) in sorted(wit.items()):
                    D, el = base_test(n - 1, E, X, Y, P2, P1, budget=2 * 10 ** 7)
                    assert D is not None, 'Prop 8.3 base not found'
                    construct.run(n - 1, E, X, Y, P2, P1, seed=y)
                print(f'  n={n}: verified far graph {verified}: base found and proof executed for {len(wit)} labelled chains', flush=True)
        print(f'n={n} graphs={count} far={far} all_r: strict-greedy={cov["sg"]} relaxed-greedy(d6_reach)={cov["rg"]} '
              f'strict-any={cov["sa"]}  (relaxed chains with y3 on P1: {y3_on_P1})', flush=True)


if __name__ == '__main__':
    main()

"""localproof.py (audit A22b): stress test of the proof of Theorem 6.1 (local girth five).

For graphs G with no vertex of positive even degree, every pair of disjoint edges e1, e2 in one
component whose four ends lie on no triangle and no 4-cycle (the LOCAL hypothesis; G itself may
have many short cycles elsewhere), every prescribed orientation (a, b) of e1 (a = prescribed
end), and EVERY shortest walk P between {a,b} and {c,d} realising the minimum (all four choices
of u, w), oriented as in the proof (u = a: y = w; u = b: exchange the edges and reverse P):

  (A) P is admissible (Def. 4.1): b, x not on P, no inner vertex adjacent to x;
  (S) the hypothesis of Theorem 5.2 holds in the base graph M: X = {x, y, a, l1} sparse and the
      pairs {x,y}, {a,l1}, {l1,y} packed, in M or in M - xv for one neighbour v of x, v not in X;
  (C) optionally (flag bf): the conclusion of Theorem 6.1 itself, by the A22 brute force bf.py
      (ab terminal at a, cd terminal at c or at d, different paths).

Written from scratch (base graph and sparse test are re-implemented here, not imported from the
A22 scripts); bf.py is imported only for (C).

Stress counters: how often the instance has short cycles elsewhere, through an inner vertex of P,
through a vertex adjacent to X in M, through the exceptional vertex v, etc.

usage: localproof.py geng "<geng args>" [bf]      e.g.  localproof.py geng "-c 8" bf
       localproof.py random COUNT SEED NMIN NMAX [bf]
"""
import sys, os, random, itertools, subprocess, signal
from collections import deque

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'A22-scripts'))


def parse_g6(s):
    s = s.strip()
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        k = ord(ch) - 63
        bits.extend((k >> i) & 1 for i in range(5, -1, -1))
    A = [[0] * n for _ in range(n)]
    t = 0
    for j in range(1, n):
        for i in range(j):
            if bits[t]:
                A[i][j] = A[j][i] = 1
            t += 1
    return n, A


def on_short_cycle(n, A):
    """bad[v] = v lies on a triangle or a 4-cycle (explicit enumeration)."""
    bad = [False] * n
    nb = [[w for w in range(n) if A[v][w]] for v in range(n)]
    for u in range(n):
        for v in nb[u]:
            for w in nb[v]:
                if w == u:
                    continue
                if A[w][u]:
                    bad[u] = bad[v] = bad[w] = True
                for t in nb[w]:
                    if t in (u, v):
                        continue
                    if A[t][u]:
                        bad[u] = bad[v] = bad[w] = bad[t] = True
    return bad


def bfs(n, A, s):
    d = [None] * n
    d[s] = 0
    q = deque([s])
    while q:
        u = q.popleft()
        for w in range(n):
            if A[u][w] and d[w] is None:
                d[w] = d[u] + 1
                q.append(w)
    return d


def all_shortest_paths(n, A, s, t, dist_t):
    """all shortest s-t paths, dist_t = BFS distances from t."""
    out = []

    def rec(p):
        u = p[-1]
        if u == t:
            out.append(list(p))
            return
        for w in range(n):
            if A[u][w] and dist_t[w] is not None and dist_t[w] == dist_t[u] - 1:
                p.append(w)
                rec(p)
                p.pop()
    rec([s])
    return out


def base(n, A, a, b, x, y, P):
    """M = ((G - ab) + l1 b) - xy - E(P); l1 = vertex n."""
    M = [row[:] + [0] for row in A] + [[0] * (n + 1)]
    for u, v in [(a, b), (x, y)] + list(zip(P, P[1:])):
        assert M[u][v], 'deleting a non-edge'
        M[u][v] = M[v][u] = 0
    M[n][b] = M[b][n] = 1
    return M


def sparse_and_packed(M, X):
    N = len(M)
    for v in range(N):
        if sum(M[v][p] for p in X) > 1:
            return False
    x, y, a, l1 = X
    for p, q in ((x, y), (a, l1), (l1, y)):
        if M[p][q] or any(M[p][w] and M[w][q] for w in range(N)):
            return False
    return True


def thm52_hyp(M, X):
    """returns (ok, exceptional vertex or None)."""
    if sparse_and_packed(M, X):
        return True, None
    x = X[0]
    for v in range(len(M)):
        if M[x][v] and v not in X:
            M[x][v] = M[v][x] = 0
            ok = sparse_and_packed(M, X)
            M[x][v] = M[v][x] = 1
            if ok:
                return True, v
    return False, None


class TO(Exception):
    pass


def _alarm(*_):
    raise TO()


def run_graph(n, A, st, use_bf, tag):
    if any(sum(r) % 2 == 0 and sum(r) > 0 for r in A):
        return
    st['graphs'] += 1
    bad = on_short_cycle(n, A)
    if not any(bad):
        st['graphs_girth5'] += 1
    E = [(u, v) for u in range(n) for v in range(u + 1, n) if A[u][v]]
    good_E = [e for e in E if not bad[e[0]] and not bad[e[1]]]
    D = {}
    for e1, e2 in itertools.permutations(good_E, 2):
        if set(e1) & set(e2):
            continue
        for v in e1 + e2:
            if v not in D:
                D[v] = bfs(n, A, v)
        c, d = e2
        if D[c][e1[0]] is None:
            continue                      # different components: Theorem 1.1 componentwise
        for a, b in (e1, e1[::-1]):
            st['instances'] += 1
            if any(bad):
                st['inst_G_not_girth5'] += 1
            k = min(D[w][u] for u in (a, b) for w in (c, d))
            for u in (a, b):
                for w in (c, d):
                    if D[w][u] != k:
                        continue
                    for P in all_shortest_paths(n, A, w, u, D[u]):
                        if u == a:
                            A_, B_, Y_ = a, b, w
                            X_ = d if w == c else c
                            PP = P
                        else:
                            A_, B_ = w, (d if w == c else c)
                            X_, Y_ = a, b
                            PP = P[::-1]
                        assert {A_, B_, X_, Y_} == {a, b, c, d}
                        st['cases'] += 1
                        adm = (B_ not in PP and X_ not in PP and PP[0] == Y_ and PP[-1] == A_
                               and all(not A[p][X_] for p in PP[1:-1]))
                        if not adm:
                            st['INADMISSIBLE'] += 1
                            print('INADMISSIBLE', tag, A_, B_, X_, Y_, PP, flush=True)
                            continue
                        M = base(n, A, A_, B_, X_, Y_, PP)
                        X = (X_, Y_, A_, n)
                        ok, v = thm52_hyp(M, X)
                        if not ok:
                            st['NOT_SPARSE'] += 1
                            print('NOT SPARSE', tag, A_, B_, X_, Y_, PP, flush=True)
                            continue
                        # stress counters
                        if any(bad[p] for p in PP[1:-1]):
                            st['inner_P_on_short_cycle'] += 1
                        nearX = {w for w in range(n) for p in (X_, Y_, A_) if M[w][p]}
                        if any(bad[w] for w in nearX):
                            st['M_nbr_of_X_on_short_cycle'] += 1
                        if v is not None:
                            st['exceptional_v'] += 1
                            if bad[v]:
                                st['exceptional_v_on_short_cycle'] += 1
            if use_bf:
                from bf import ptm_assign
                G = [row[:] for row in A]
                signal.alarm(60)
                try:
                    res = (ptm_assign(n, G, [(a, b), (c, d)], [a, c]) or
                           ptm_assign(n, G, [(a, b), (c, d)], [a, d]))
                    signal.alarm(0)
                except TO:
                    res = None
                if res is None:
                    st['bf_timeout'] += 1
                elif res:
                    st['bf_ok'] += 1
                else:
                    st['BF_FAIL'] += 1
                    print('BF FAIL', tag, a, b, c, d, flush=True)


def new_stats():
    keys = ['graphs', 'graphs_girth5', 'instances', 'inst_G_not_girth5', 'cases', 'INADMISSIBLE',
            'NOT_SPARSE', 'inner_P_on_short_cycle', 'M_nbr_of_X_on_short_cycle', 'exceptional_v',
            'exceptional_v_on_short_cycle', 'bf_ok', 'bf_timeout', 'BF_FAIL']
    return {k: 0 for k in keys}


def random_odd_graph(rng, n):
    """random simple graph with all degrees odd in {1,3,5} (configuration model, simple kept),
    possibly disconnected; then a few isolated vertices appended."""
    while True:
        degs = [rng.choice((1, 3, 3, 3, 3, 5)) for _ in range(n)]
        if sum(degs) % 2:
            continue
        stubs = [v for v in range(n) for _ in range(degs[v])]
        rng.shuffle(stubs)
        A = [[0] * n for _ in range(n)]
        ok = True
        for i in range(0, len(stubs), 2):
            u, v = stubs[i], stubs[i + 1]
            if u == v or A[u][v]:
                ok = False
                break
            A[u][v] = A[v][u] = 1
        if ok:
            iso = rng.choice((0, 0, 1, 2))
            for row in A:
                row.extend([0] * iso)
            A.extend([[0] * (n + iso) for _ in range(iso)])
            return n + iso, A


def main():
    signal.signal(signal.SIGALRM, _alarm)
    st = new_stats()
    if sys.argv[1] == 'geng':
        use_bf = len(sys.argv) > 3 and sys.argv[3] == 'bf'
        proc = subprocess.Popen(['nauty-geng', '-q'] + sys.argv[2].split(), stdout=subprocess.PIPE,
                                text=True)
        for line in proc.stdout:
            n, A = parse_g6(line)
            run_graph(n, A, st, use_bf, line.strip())
        print('geng', sys.argv[2], st, flush=True)
    else:
        count, seed, nmin, nmax = map(int, sys.argv[2:6])
        use_bf = len(sys.argv) > 6 and sys.argv[6] == 'bf'
        rng = random.Random(seed)
        for i in range(count):
            n, A = random_odd_graph(rng, rng.randint(nmin, nmax))
            run_graph(n, A, st, use_bf, 'rnd%d' % i)
        print('random', count, seed, nmin, nmax, st, flush=True)


if __name__ == '__main__':
    main()

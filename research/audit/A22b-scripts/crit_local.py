"""crit_local.py (audit A22b): test the criterion after Corollary 7.2.

Claim: for H = J - z and distinct a, b, c, d with ab, cd not edges of H,
  "no cycle of length <= 4 of J* = H + ab + cd passes through a, b, c or d"
iff
  (i)   no cycle of length <= 4 of H passes through a, b, c or d,
  (ii)  d_H(a,b) >= 4 and d_H(c,d) >= 4,
  (iii) d_H(a,c) + d_H(b,d) >= 3 and d_H(a,d) + d_H(b,c) >= 3.
Also the global variant: girth(J*) >= 5 iff girth(H) >= 5 and (ii), (iii).

(z is isolated in J*, so it is irrelevant for cycles; H is a graph on n vertices.)

Three independent short-cycle detectors are used and cross-checked:
  T: explicit enumeration of vertex tuples (u v w) / (u v w t) with u in S;
  E: s lies on a cycle of length <= 4 iff some edge su has d_{G - su}(s, u) <= 3;
  N: neighbour-pair test (triangle s u v, or 4-cycle s u w v with w != s), as in
     scripts/localgirth_stat.py.
No networkx; adjacency as bit masks.

usage: crit_local.py exhaustive NMAX     (all labelled H on n <= NMAX vertices, a,b,c,d = 0,1,2,3)
       crit_local.py random COUNT SEED   (random H, random a,b,c,d, n in 4..14)
"""
import sys, random, itertools

INF = 10 ** 6


def bfs_dist(adj, n, s, t, skip=None):
    """distance from s to t, optionally ignoring the edge skip = (p, q)."""
    if s == t:
        return 0
    dist = {s: 0}
    frontier = [s]
    while frontier:
        nxt = []
        for u in frontier:
            m = adj[u]
            for w in range(n):
                if m >> w & 1 and w not in dist:
                    if skip is not None and {u, w} == set(skip):
                        continue
                    dist[w] = dist[u] + 1
                    if w == t:
                        return dist[w]
                    nxt.append(w)
        frontier = nxt
    return INF


def short_T(adj, n, S):
    A = lambda u, v: adj[u] >> v & 1
    for u in S:
        for v in range(n):
            if not A(u, v):
                continue
            for w in range(n):
                if w in (u, v) or not A(v, w):
                    continue
                if A(w, u):
                    return True
                for t in range(n):
                    if t in (u, v, w):
                        continue
                    if A(w, t) and A(t, u):
                        return True
    return False


def short_E(adj, n, S):
    for s in S:
        for u in range(n):
            if adj[s] >> u & 1 and bfs_dist(adj, n, s, u, skip=(s, u)) <= 3:
                return True
    return False


def short_N(adj, n, S):
    for s in S:
        nb = [u for u in range(n) if adj[s] >> u & 1]
        for u, v in itertools.combinations(nb, 2):
            if adj[u] >> v & 1:
                return True
            if adj[u] & adj[v] & ~(1 << s):
                return True
    return False


def check(adj, n, a, b, c, d, stats):
    S = (a, b, c, d)
    js = list(adj)
    js[a] |= 1 << b; js[b] |= 1 << a
    js[c] |= 1 << d; js[d] |= 1 << c
    lhsT, lhsE, lhsN = short_T(js, n, S), short_E(js, n, S), short_N(js, n, S)
    assert lhsT == lhsE == lhsN, ('detector disagreement on J*', adj, S)
    lhs = not lhsT
    hT = short_T(adj, n, S)
    assert hT == short_E(adj, n, S) == short_N(adj, n, S)
    D = lambda u, v: bfs_dist(adj, n, u, v)
    rhs = (not hT and D(a, b) >= 4 and D(c, d) >= 4 and D(a, c) + D(b, d) >= 3
           and D(a, d) + D(b, c) >= 3)
    stats['tests'] += 1
    stats['lhs_true'] += lhs
    if lhs != rhs:
        stats['mismatch'] += 1
        print('MISMATCH', n, adj, S, lhs, rhs)
    # global variant
    allv = range(n)
    g_lhs = not short_N(js, n, allv)
    g_rhs = (not short_N(adj, n, allv) and D(a, b) >= 4 and D(c, d) >= 4
             and D(a, c) + D(b, d) >= 3 and D(a, d) + D(b, c) >= 3)
    stats['g_true'] += g_lhs
    if g_lhs != g_rhs:
        stats['g_mismatch'] += 1
        print('GLOBAL MISMATCH', n, adj, S, g_lhs, g_rhs)
    # sanity: local hypothesis strictly weaker than global girth five
    if lhs and not g_lhs:
        stats['local_not_global'] += 1


def main():
    mode = sys.argv[1]
    stats = dict(tests=0, lhs_true=0, mismatch=0, g_true=0, g_mismatch=0, local_not_global=0)
    if mode == 'exhaustive':
        for n in range(4, int(sys.argv[2]) + 1):
            pairs = [(u, v) for u in range(n) for v in range(u + 1, n) if (u, v) not in ((0, 1), (2, 3))]
            for mask in range(1 << len(pairs)):
                adj = [0] * n
                for i, (u, v) in enumerate(pairs):
                    if mask >> i & 1:
                        adj[u] |= 1 << v; adj[v] |= 1 << u
                check(adj, n, 0, 1, 2, 3, stats)
            print('n<=%d' % n, stats, flush=True)
    else:
        count, seed = int(sys.argv[2]), int(sys.argv[3])
        rng = random.Random(seed)
        while stats['tests'] < count:
            n = rng.randint(4, 14)
            p = rng.choice([0.08, 0.12, 0.18, 0.25, 0.35, 0.5])
            adj = [0] * n
            for u in range(n):
                for v in range(u + 1, n):
                    if rng.random() < p:
                        adj[u] |= 1 << v; adj[v] |= 1 << u
            a, b, c, d = rng.sample(range(n), 4)
            if adj[a] >> b & 1 or adj[c] >> d & 1:
                continue
            check(adj, n, a, b, c, d, stats)
        print('random', stats)


if __name__ == '__main__':
    main()

"""Audit A22c: admissible chains (Definition 8.1), base graphs, and the base test of Theorem 8.2,
written from the manuscript (not from walk3.c).

G is simple: a vertex count n and a set of edges (frozensets).  A configuration is
X = (x1, x2, x3), Y = (y1, y2, y3) with x_i y_i the edges of F (x_i short).
Variants of Definition 8.1 are selected by flags (default = the literal definition, N(.) in G).
"""
import itertools
from collections import deque
from dlib import solve, check_decomp, check_constraints

FLAGS = dict(
    nbrH=False,      # N(.) taken in G - F instead of G (allows y3 inside P1)
    allow_y1=False,  # drop "y1 not on P1, P2"
    no_y2x3=False,   # drop "y2 not in N(x3)"
    no_P1N2=False,   # drop "inner p_i not in N(x2)"
    no_P1N3=False,   # drop "inner p_i not in N(x3)"
    no_P2N3=False,   # drop "inner q_i not in N(x3)"
    allow_x1_P2=False,  # drop "x1 not on P2"
    allow_y2_P2=False,  # drop "y2 not on P2"
)


def adjsets(n, E):
    A = [set() for _ in range(n)]
    for e in E:
        a, b = tuple(e)
        A[a].add(b); A[b].add(a)
    return A


def configs(F):
    """all 48 labelled configurations of the matching F (3 pairs)"""
    for perm in itertools.permutations(range(3)):
        for o in range(8):
            X = tuple(F[perm[i]][(o >> i) & 1] for i in range(3))
            Y = tuple(F[perm[i]][1 - ((o >> i) & 1)] for i in range(3))
            yield X, Y


def rules(n, E, X, Y, fl):
    """returns (start/end/inner predicates) for P2 and P1, the walk graph adjacency (G - F), and
    the global precondition y2 not in N(x3)"""
    x1, x2, x3 = X; y1, y2, y3 = Y
    Fset = {frozenset((X[i], Y[i])) for i in range(3)}
    GF = adjsets(n, [e for e in E if e not in Fset])
    NG = adjsets(n, E)
    N = GF if fl['nbrH'] else NG
    pre = fl['no_y2x3'] or (y2 not in N[x3])
    ban2 = {x1, y1, y2, x3, x2}
    if fl['allow_y1']: ban2.discard(y1)
    if fl['allow_x1_P2']: ban2.discard(x1)
    if fl['allow_y2_P2']: ban2.discard(y2)
    def inner2(w):
        if w in ban2: return False
        if not fl['no_P2N3'] and w in N[x3]: return False
        return True
    ban1 = {y1, x2, x3, x1}
    if fl['allow_y1']: ban1.discard(y1)
    def inner1(w):
        if w in ban1: return False
        if not fl['no_P1N2'] and w in N[x2]: return False
        if not fl['no_P1N3'] and w in N[x3]: return False
        return True
    return GF, pre, inner2, inner1


def bfs_len(adj, s, t, inner, banned=frozenset()):
    dist = {s: 0}; q = deque([s])
    while q:
        v = q.popleft()
        if v == t:
            return dist[v]
        for w in adj[v]:
            if w in dist or frozenset((v, w)) in banned:
                continue
            if w != t and not inner(w):
                continue
            dist[w] = dist[v] + 1; q.append(w)
    return None


def paths(adj, s, t, inner, maxlen, banned=frozenset()):
    """all simple paths s -> t (vertex lists) of length <= maxlen, inner vertices satisfying inner,
    edges not in banned; the end t only as last vertex"""
    out = []
    def dfs(p):
        v = p[-1]
        if v == t:
            out.append(list(p)); return
        if len(p) - 1 >= maxlen:
            return
        for w in sorted(adj[v]):
            if w in p or frozenset((v, w)) in banned:
                continue
            if w != t and not inner(w):
                continue
            p.append(w); dfs(p); p.pop()
    dfs([s])
    return out


def pedges(P):
    return {frozenset((P[i], P[i + 1])) for i in range(len(P) - 1)}


def chains(n, E, X, Y, fl=FLAGS, mode='walk3', maxlen=None):
    """yield admissible chains (P2, P1).  mode 'walk3': P2 of the least constrained length, P1 of
    length at most the least constrained length of P1 (computed without P2), edge-disjoint;
    mode 'all': all lengths (<= maxlen if given)."""
    x1, x2, x3 = X; y1, y2, y3 = Y
    GF, pre, inner2, inner1 = rules(n, E, X, Y, fl)
    if not pre:
        return
    if mode == 'walk3':
        d2 = bfs_len(GF, y3, x2, inner2); d1 = bfs_len(GF, y2, x1, inner1)
        if d2 is None or d1 is None:
            return
        L2, L1 = d2, d1
    else:
        L2 = L1 = maxlen if maxlen is not None else n
    for P2 in paths(GF, y3, x2, inner2, L2):
        for P1 in paths(GF, y2, x1, inner1, L1, banned=pedges(P2)):
            yield P2, P1


def has_walks(n, E, X, Y, fl=FLAGS):
    GF, pre, inner2, inner1 = rules(n, E, X, Y, fl)
    if not pre:
        return False
    return bfs_len(GF, Y[2], X[1], inner2) is not None and bfs_len(GF, Y[1], X[0], inner1) is not None


def base_graph(n, E, X, Y, P2, P1):
    """M = ((G - x1y1) + l1 y1) - x2y2 - x3y3 - E(P1) - E(P2), l1 = n.  Returns edge list."""
    Fset = {frozenset((X[i], Y[i])) for i in range(3)}
    rem = set(E) - Fset - pedges(P1) - pedges(P2)
    assert not (pedges(P1) & pedges(P2)) and not (pedges(P1) & Fset) and not (pedges(P2) & Fset)
    el = [tuple(sorted(e)) for e in rem] + [(Y[0], n)]
    return el


def six_pairs(X, Y, l1):
    x1, x2, x3 = X; y1, y2, y3 = Y
    return [(x1, l1), (x2, y2), (x3, y3), (l1, y2), (l1, y3), (y2, y3)]


def base_test(n, E, X, Y, P2, P1, seed=1, budget=0):
    el = base_graph(n, E, X, Y, P2, P1)
    N = n + 1
    deg = [0] * N
    for a, b in el:
        deg[a] += 1; deg[b] += 1
    ev = [v for v in range(N) if deg[v] > 0 and deg[v] % 2 == 0]
    assert ev in ([], [X[2]]), ('parity', ev, X)
    ends = {v for v in range(N) if deg[v] % 2 == 1}
    seps = six_pairs(X, Y, n)
    D = solve(N, el, ends, seps=seps, seed=seed, budget=budget)
    if D is not None:
        check_decomp(N, el, D, ends); check_constraints(D, seps=seps)
    return D, el

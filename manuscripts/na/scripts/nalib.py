"""Constructive implementation of the proofs in manuscripts/na.

Everything here follows the written proofs step by step:
  * fan(...)          Fan's lemma with vertex sets (route-descent Lemma 2.2), general chain search;
  * separation(...)   the separation theorem for packed sets (route-descent Thm 6.1), Cases I-IV;
  * l1(...)           L1 in set form (route-descent Thm 6.3), via the pendant-leaf trick;
  * exhausting_trail  the trail lemma of the manuscript (good vertex, T-join, Euler trail);
  * na_construct      the main theorem: pendant leaf at y, steered Case-I chain, L1, Fan back-steps.
The verifier `check_lovasz` is independent of the construction.

Graphs are dicts {vertex: set(neighbours)}; paths are lists of vertices.
"""
import sys
from collections import deque

sys.setrecursionlimit(100000)


# ---------------------------------------------------------------- graph helpers
def copy_graph(G):
    return {v: set(N) for v, N in G.items()}


def add_edge(G, a, b):
    assert a != b and b not in G.setdefault(a, set())
    G[a].add(b)
    G.setdefault(b, set()).add(a)


def del_edge(G, a, b):
    G[a].remove(b)
    G[b].remove(a)


def deg(G, v):
    return len(G.get(v, ()))


def even_vertices(G):
    return [v for v in G if deg(G, v) > 0 and deg(G, v) % 2 == 0]


def edges_of(G):
    return {frozenset((a, b)) for a in G for b in G[a] if a < b} if all(
        isinstance(v, int) for v in G) else {frozenset((a, b)) for a in G for b in G[a]}


def path_edges(P):
    return [frozenset((P[i], P[i + 1])) for i in range(len(P) - 1)]


def ends_count(D):
    b = {}
    for P in D:
        for e in (P[0], P[-1]):
            b[e] = b.get(e, 0) + 1
    return b


def packed(G, X):
    X = list(X)
    for i in range(len(X)):
        for j in range(i + 1, len(X)):
            a, c = X[i], X[j]
            if c in G.get(a, ()):
                return False
            if G.get(a, set()) & G.get(c, set()):
                return False
    return True


# ---------------------------------------------------------------- verifier (independent)
def check_lovasz(G, D):
    """D is a Lovasz decomposition of G: a partition of E(G) into paths with b(v) = d(v) mod 2."""
    seen = set()
    for P in D:
        if len(P) < 2 or len(set(P)) != len(P):
            return False, "not a path: %r" % (P,)
        for e in path_edges(P):
            a, c = tuple(e)
            if c not in G.get(a, ()):
                return False, "non-edge %r" % (e,)
            if e in seen:
                return False, "edge used twice %r" % (e,)
            seen.add(e)
    allE = {frozenset((a, c)) for a in G for c in G[a]}
    if seen != allE:
        return False, "edges not covered"
    b = ends_count(D)
    for v in G:
        if b.get(v, 0) != deg(G, v) % 2:
            return False, "wrong ends at %r: %d" % (v, b.get(v, 0))
    for v in b:
        if v not in G:
            return False, "end at foreign vertex"
    return True, ""


def path_ending_at(D, c):
    Ps = [P for P in D if P[0] == c or P[-1] == c]
    assert len(Ps) == 1, (c, Ps)
    return Ps[0]


# ---------------------------------------------------------------- Fan's lemma
def fan(K, D, t, u):
    """K: graph (not containing edge tu), D: path partition of K with b(t) > |Z(u)|.
    Returns a path partition of K + tu with b' = b - 1_t + 1_u, every path keeping its vertex set
    except one, which gains u (route-descent Lemma 2.2). K is not modified."""
    assert t != u and u not in K.get(t, set())
    b = ends_count(D)
    Z = [w for w in K.get(u, ()) if b.get(w, 0) == 0]
    assert b.get(t, 0) > len(Z), "Fan hypothesis fails"
    D = [list(P) for P in D]

    def pi(x, P):  # vertex before u on P read from x
        Q = P if P[0] == x else P[::-1]
        i = Q.index(u)
        return Q[i - 1]

    # BFS over vertices; for each x the paths ending at x
    def paths_at(x):
        return [i for i, P in enumerate(D) if P[0] == x or P[-1] == x]

    parent = {t: None}
    order = deque([t])
    found = None
    while order and found is None:
        x = order.popleft()
        for i in paths_at(x):
            if u not in D[i]:
                found = (x, i)
                break
        if found:
            break
        for i in paths_at(x):
            y = pi(x, D[i])
            if y not in parent:
                parent[y] = (x, i)
                order.append(y)
    assert found is not None, "no chain (Fan hypothesis should prevent this)"
    xk, istar = found
    chain = []  # list of (x_i, path index) for i<k
    v = xk
    while parent[v] is not None:
        x, i = parent[v]
        chain.append((x, i))
        v = x
    chain.reverse()
    xs = [c[0] for c in chain] + [xk]
    assert len(set(xs)) == len(xs)
    # execute re-routings
    for j, (x, i) in enumerate(chain):
        P = D[i]
        Q = P if P[0] == x else P[::-1]
        assert Q[0] == x
        iu = Q.index(u)
        nxt = Q[iu - 1]
        assert nxt == xs[j + 1], "re-routing reads a different predecessor"
        # Q = x ... nxt u ... yend  ->  nxt ... x u ... yend
        seg = Q[:iu]          # x ... nxt
        rest = Q[iu:]         # u ... yend
        D[i] = seg[::-1] + rest
    # append
    P = D[istar]
    assert u not in P
    if P[-1] == xk:
        D[istar] = P + [u]
    else:
        assert P[0] == xk
        D[istar] = [u] + P
    return D


# ---------------------------------------------------------------- separation theorem
_leaf_counter = [0]


def new_vertex(G):
    _leaf_counter[0] += 1
    v = ("leaf", _leaf_counter[0])
    while v in G:
        _leaf_counter[0] += 1
        v = ("leaf", _leaf_counter[0])
    return v


def separation(K, X):
    """K with at most one vertex of positive even degree, X packed in K. Returns a Lovasz
    decomposition of K in which every path meets X at most once (route-descent Thm 6.1)."""
    K = copy_graph(K)
    X = set(X)
    ev = even_vertices(K)
    assert len(ev) <= 1
    if ev:  # Case I
        z = ev[0]
        us = [u for u in K[z] if u not in X]
        assert us
        u = min(us, key=repr)
        del_edge(K, u, z)
        Dp = separation(K, X)
        D = fan(K, Dp, z, u)
        return D
    big = [v for v in K if v not in X and deg(K, v) >= 3]
    if big:  # Case II
        x = min(big, key=repr)
        u = min(K[x], key=repr)
        H = copy_graph(K)
        del_edge(H, x, u)
        l = new_vertex(H)
        add_edge(H, u, l)
        DH = separation(H, X)
        D = []
        bu = 0
        for P in DH:
            if l in P:
                Q = P if P[-1] == l else P[::-1]
                Q = Q[:-1]
                if len(Q) >= 2:
                    D.append(Q)
            else:
                D.append(P)
        Kp = copy_graph(K)
        del_edge(Kp, x, u)
        b = ends_count(D)
        if b.get(u, 0) == 0:
            D.append([u, x])
            return D
        assert b.get(u, 0) == 2
        return fan(Kp, D, u, x)
    ones = [v for v in K if v not in X and deg(K, v) == 1]
    if ones:  # Case III
        v = min(ones, key=repr)
        w = next(iter(K[v]))
        del_edge(K, v, w)
        D = separation(K, X)
        return D + [[v, w]]
    # Case IV
    assert all(deg(K, v) == 0 for v in K if v not in X)
    assert all(deg(K, v) == 0 for v in K), "Case IV with an edge"
    return []


def l1(F, c, Y):
    """F with no vertex of positive even degree, c odd, Y packed, Y disjoint from N[c].
    Returns a Lovasz decomposition with every path meeting Y at most once and Q_c avoiding Y."""
    Y = set(Y)
    assert not even_vertices(F)
    assert deg(F, c) % 2 == 1
    assert c not in Y and not (F[c] & Y) and packed(F, Y)
    K = copy_graph(F)
    l = new_vertex(K)
    add_edge(K, c, l)
    DK = separation(K, Y | {l})
    D = []
    for P in DK:
        if l in P:
            Q = P if P[-1] == l else P[::-1]
            Q = Q[:-1]
            assert len(Q) >= 2 and Q[-1] == c
            D.append(Q)
        else:
            D.append(P)
    return D


# ---------------------------------------------------------------- the trail lemma
def components(G, verts=None):
    verts = set(G) if verts is None else set(verts)
    comp = {}
    out = []
    for s in verts:
        if s in comp:
            continue
        cur = [s]
        comp[s] = len(out)
        stack = [s]
        while stack:
            a = stack.pop()
            for c in G[a]:
                if c in verts and c not in comp:
                    comp[c] = len(out)
                    cur.append(c)
                    stack.append(c)
        out.append(cur)
    return out


def bfs_path(G, s, t, banned=()):
    prev = {s: None}
    dq = deque([s])
    while dq:
        a = dq.popleft()
        if a == t:
            break
        for c in G[a]:
            if c not in prev and c not in banned:
                prev[c] = a
                dq.append(c)
    assert t in prev
    P = [t]
    while prev[P[-1]] is not None:
        P.append(prev[P[-1]])
    return P[::-1]


def exhausting_trail(C, y):
    """C connected graph (dict), d_C(y) even, C has an odd vertex. Returns a trail
    [y = g0, g1, ..., gk = t] with distinct edges, t odd, using every edge of C at t.
    Construction of the manuscript: a good odd vertex t, a T-join J in C - t for
    T = (odd(C) - t) + y, and an Euler trail of the component of C - J containing t."""
    odd = [v for v in C if deg(C, v) % 2 == 1]
    assert odd and deg(C, y) % 2 == 0

    def bad_component(t):
        Ct = {v: set(N) - {t} for v, N in C.items() if v != t}
        for comp in components(Ct):
            if y in comp:
                continue
            e = sum(1 for v in comp if t in C[v])
            if e % 2 == 1:
                return set(comp)
        return None

    # choose a bad pair with a minimal bad component, then descend (proof of the lemma)
    t = odd[0]
    D = bad_component(t)
    while D is not None:
        cands = [v for v in D if deg(C, v) % 2 == 1]
        assert cands
        t2 = cands[0]
        D2 = bad_component(t2)
        if D2 is not None:
            assert D2 < D, "descent failed: bad component did not shrink"
        t, D = t2, D2
    # T-join in C - t
    Ct = {v: set(N) - {t} for v, N in C.items() if v != t}
    T = set(v for v in odd if v != t) ^ {y}
    J = set()
    for comp in components(Ct):
        Tc = [v for v in comp if v in T]
        assert len(Tc) % 2 == 0
        for i in range(0, len(Tc), 2):
            P = bfs_path(Ct, Tc[i], Tc[i + 1])
            J ^= set(path_edges(P))
    S = {v: set() for v in C}
    for a in C:
        for c in C[a]:
            if frozenset((a, c)) not in J:
                S[a].add(c)
    oddS = [v for v in S if len(S[v]) % 2 == 1]
    assert sorted(map(repr, oddS)) == sorted(map(repr, [t, y])), (oddS, t, y)
    assert S[t] == C[t]
    # Hierholzer: Euler trail from t in the component of S containing t
    Sw = copy_graph(S)
    stack = [t]
    circ = []
    while stack:
        a = stack[-1]
        if Sw[a]:
            c = min(Sw[a], key=repr)
            del_edge(Sw, a, c)
            stack.append(c)
        else:
            circ.append(stack.pop())
    W = circ[::-1]  # Euler trail from t to y (Hierholzer gives it starting at t)
    assert W[0] == t and W[-1] == y, (W, t, y)
    W = W[::-1]  # from y to t
    es = path_edges(W)
    assert len(set(es)) == len(es)
    assert all(frozenset((t, c)) in set(es) for c in C[t])
    return W


def trail_exists_bruteforce(C, y):
    """Is there a trail from y ending at an odd vertex t using all edges at t?"""
    odd = set(v for v in C if deg(C, v) % 2 == 1)

    def rec(G, cur, first):
        if not first and cur in odd and deg(G, cur) == 0:
            return True
        for c in list(G[cur]):
            del_edge(G, cur, c)
            ok = rec(G, c, False)
            add_edge(G, cur, c)
            if ok:
                return True
        return False

    return rec(copy_graph(C), y, True)


# ---------------------------------------------------------------- main construction
def na_construct(G, y, Y):
    """G: all degrees odd or zero; Y packed; y not in Y, d(y) >= 1; the component of y in G - Y
    contains a vertex outside N(Y). Returns a Lovasz decomposition of G in which every path meets
    Y at most once and the path ending at y avoids Y. Also returns the trail used (or None)."""
    Y = set(Y)
    assert not even_vertices(G) and deg(G, y) % 2 == 1 and y not in Y and packed(G, Y)
    NY = set()
    for a in Y:
        NY |= G[a]
    if y not in NY:
        return l1(G, y, Y), None
    # pendant leaf at y
    K = copy_graph(G)
    l = new_vertex(K)
    add_edge(K, y, l)
    # H = G - Y, component of y
    Hv = [v for v in G if v not in Y]
    H = {v: set(G[v]) - Y for v in Hv}
    comp = next(c for c in components(H) if y in c)
    C = {v: set(H[v]) for v in comp}
    assert any(v not in NY for v in comp), "witness hypothesis fails"
    W = exhausting_trail(C, y)
    t = W[-1]
    assert t not in NY and t != y
    # forward: K_0 = K, K_{i+1} = K_i - g_i g_{i+1}
    Ks = [copy_graph(K)]
    for i in range(len(W) - 1):
        Ki = Ks[-1]
        ev = even_vertices(Ki)
        assert ev == [W[i]], (ev, W[i])
        a, c = W[i], W[i + 1]
        assert c not in Y and c != l
        Kn = copy_graph(Ki)
        del_edge(Kn, a, c)
        Ks.append(Kn)
    Kk = Ks[-1]
    assert not even_vertices(Kk) and deg(Kk, t) == 0
    D = l1(Kk, l, Y)
    # backward Fan steps, target g_{i+1}
    for i in range(len(W) - 2, -1, -1):
        D = fan(Ks[i + 1], D, W[i], W[i + 1])
    ok, msg = check_lovasz(K, D)
    assert ok, msg
    # remove the leaf
    out = []
    for P in D:
        if l in P:
            Q = P if P[-1] == l else P[::-1]
            Q = Q[:-1]
            assert len(Q) >= 2 and Q[-1] == y
            out.append(Q)
        else:
            out.append(P)
    return out, W


def check_na_output(G, D, y, Y):
    ok, msg = check_lovasz(G, D)
    if not ok:
        return False, msg
    Q = path_ending_at(D, y)
    if set(Q) & set(Y):
        return False, "Q(y) meets Y"
    for P in D:
        if len(set(P) & set(Y)) > 1:
            return False, "a path meets Y twice"
    return True, ""


# ---------------------------------------------------------------- graph6
def g6_decode(s):
    s = s.strip()
    data = [ord(ch) - 63 for ch in s]
    if data[0] == 63:
        n = (data[1] << 12) | (data[2] << 6) | data[3]
        data = data[4:]
    else:
        n = data[0]
        data = data[1:]
    bits = []
    for d in data:
        for k in range(5, -1, -1):
            bits.append((d >> k) & 1)
    G = {v: set() for v in range(n)}
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                G[i].add(j)
                G[j].add(i)
            k += 1
    return G

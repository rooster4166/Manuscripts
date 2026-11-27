"""A24 audit: independent library (does NOT import tf.py).

Graphs: dict v -> frozenset/set of neighbours.  Own graph6 decoder.
Decompositions: list of tuples of vertices (paths with >= 1 edge).

* g6(s)                 -- decode graph6 (own code)
* decomps_pg(G, b, first_edges=None, path_ok=None)
                        -- enumerate every path decomposition with end counts b by PATH GROWING
                           (a different algorithm from tf.py's transition systems):
                           repeatedly take the smallest uncovered edge (or a prescribed one first)
                           and enumerate every simple path through it in the uncovered graph.
                           path_ok(P) may veto a path (used to prune the protected path).
* verify(G, D, b)       -- independent checker
* forced_chain(D, t, w) -- Fan's chain read off D when b <= 1 (RD Lemma 2.2), returns
                           ('ok', chain) or ('stuck', chain)
* exec_chain(D, chain, w) -- execute the chain exactly as in RD Lemma 2.2 (reroutes + append)
* all_fan_results(D, t, w) -- every result of Fan's argument over ALL chains of distinct vertices
                           (general definition, any number of ends), to test uniqueness
"""
import itertools, collections


def g6(s):
    data = [ord(ch) - 63 for ch in s.strip()]
    n = data[0]
    assert n < 63
    bits = []
    for x in data[1:]:
        for k in range(5, -1, -1):
            bits.append((x >> k) & 1)
    G = {v: set() for v in range(n)}
    idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                G[i].add(j); G[j].add(i)
            idx += 1
    return G


def copyg(G):
    return {v: set(G[v]) for v in G}


def deledge(G, *es):
    H = copyg(G)
    for a, b in es:
        assert b in H[a]
        H[a].discard(b); H[b].discard(a)
    return H


def addedge(G, *es):
    H = copyg(G)
    for a, b in es:
        H.setdefault(a, set()); H.setdefault(b, set())
        assert b not in H[a] and a != b
        H[a].add(b); H[b].add(a)
    return H


def edgelist(G):
    return sorted((a, b) for a in G for b in G[a] if a < b)


def evens(G):
    return [v for v in G if len(G[v]) > 0 and len(G[v]) % 2 == 0]


def lov(G):
    return {v: len(G[v]) % 2 for v in G}


def nends(D, v):
    return sum((P[0] == v) + (P[-1] == v) for P in D)


def paths_ending(D, v):
    return [i for i, P in enumerate(D) if P[0] == v or P[-1] == v]


def verify(G, D, b=None):
    seen = set()
    for P in D:
        if len(P) < 2 or len(set(P)) != len(P):
            return False
        for x, y in zip(P, P[1:]):
            if y not in G[x]:
                return False
            e = (min(x, y), max(x, y))
            if e in seen:
                return False
            seen.add(e)
    if seen != set(edgelist(G)):
        return False
    if b is not None:
        for v in G:
            if nends(D, v) != b.get(v, 0):
                return False
    return True


def bfs_dist(G, s):
    d = {s: 0}; q = [s]
    for x in q:
        for y in G[x]:
            if y not in d:
                d[y] = d[x] + 1; q.append(y)
    return d


def connected(G):
    vs = [v for v in G]
    if not vs:
        return True
    return len(bfs_dist(G, vs[0])) == len(vs)


# ---------------------------------------------------------------------------
# enumeration by path growing

def decomps_pg(G, b, first_edges=(), path_ok=None):
    """Yield every path decomposition of G with end counts b (dict).  Each decomposition is
    produced exactly once: the path through the current pivot edge is unique.
    first_edges: edges to use as pivots first (in this order) -- lets the caller treat the
    protected path first.  path_ok(P): optional veto on a path."""
    rem = {v: set(G[v]) for v in G}
    endc = {v: 0 for v in G}
    E = edgelist(G)
    order = [tuple(sorted(e)) for e in first_edges] + [e for e in E if e not in
                                                       {tuple(sorted(f)) for f in first_edges}]
    D = []

    def feasible(v):
        need = b.get(v, 0) - endc[v]
        r = len(rem[v])
        return need >= 0 and need <= r and (need - r) % 2 == 0

    def rec(k):
        while k < len(order) and order[k][1] not in rem[order[k][0]]:
            k += 1
        if k == len(order):
            if all(endc[v] == b.get(v, 0) for v in G):
                yield list(D)
            return
        x, y = order[k]
        # remove pivot edge
        rem[x].discard(y); rem[y].discard(x)
        # grow right part from y (not visiting x), then left from x
        right = [y]; used = {x, y}
        yield from grow_right(k, x, right, used)
        rem[x].add(y); rem[y].add(x)

    def grow_right(k, x, right, used):
        # option: stop right part here
        yield from grow_left(k, [x], right, used)
        tip = right[-1]
        for z in sorted(rem[tip]):
            if z in used:
                continue
            rem[tip].discard(z); rem[z].discard(tip)
            used.add(z); right.append(z)
            yield from grow_right(k, x, right, used)
            right.pop(); used.discard(z)
            rem[tip].add(z); rem[z].add(tip)

    def grow_left(k, left, right, used):
        # option: stop: path = reversed(left) + right
        P = tuple(reversed(left)) + tuple(right)
        a, c = P[0], P[-1]
        endc[a] += 1; endc[c] += 1
        ok = True
        if path_ok is not None and not path_ok(P):
            ok = False
        if ok:
            # feasibility at the two ends and at all vertices of P (their rem changed)
            for v in P:
                if not feasible(v):
                    ok = False; break
        if ok:
            D.append(P)
            yield from rec(k + 1)
            D.pop()
        endc[a] -= 1; endc[c] -= 1
        tip = left[-1]
        for z in sorted(rem[tip]):
            if z in used:
                continue
            rem[tip].discard(z); rem[z].discard(tip)
            used.add(z); left.append(z)
            yield from grow_left(k, left, right, used)
            left.pop(); used.discard(z)
            rem[tip].add(z); rem[z].add(tip)

    yield from rec(0)


def canon(D):
    return frozenset(P if P[0] < P[-1] else tuple(reversed(P)) for P in D)


# ---------------------------------------------------------------------------
# Fan's chain

def orient_from(P, x):
    if P[0] == x:
        return P
    assert P[-1] == x
    return tuple(reversed(P))


def forced_chain(D, t, w):
    """D with at most one end at every chain vertex.  Returns (status, chain, idxs) where
    status 'ok' (last path avoids w), or 'stuck' (a vertex with no end reached), and idxs the
    indices (in D) of the paths Q_0..Q_k used."""
    chain = [t]; idxs = []
    x = t
    while True:
        I = paths_ending(D, x)
        if len(I) == 0:
            return 'stuck', chain, idxs
        assert len(I) == 1, ("more than one end at", x)
        i = I[0]; P = orient_from(D[i], x)
        idxs.append(i)
        if w not in P:
            return 'ok', chain, idxs
        k = P.index(w)
        z = P[k - 1]
        assert k >= 1 and z != x, "edge xw present?"
        if z in chain:
            raise AssertionError("chain repeats")
        chain.append(z); x = z


def exec_chain(D, chain, idxs, w):
    """RD Lemma 2.2: reroute Q_i at x_i (i < k), then append x_k w to Q_k."""
    cur = list(D)
    k = len(chain) - 1
    for i in range(k):
        xi, xn = chain[i], chain[i + 1]
        P = cur[idxs[i]]
        Po = orient_from(P, xi)
        j = Po.index(w)
        assert Po[j - 1] == xn
        # x_i ... x_{i+1} w ... y  ->  x_{i+1} ... x_i w ... y
        cur[idxs[i]] = tuple(reversed(Po[:j])) + Po[j:]
    P = cur[idxs[k]]
    Po = orient_from(P, chain[k])
    assert w not in Po
    cur[idxs[k]] = (w,) + Po
    return cur


def all_fan_results(D, t, w):
    """Every decomposition produced by Fan's argument (RD Lemma 2.2) over all chains
    t = x_0, ..., x_k of DISTINCT vertices with paths Q_i in D (general: several ends allowed).
    Returns the set of canonical results."""
    res = set()

    def rec(chain, qs):
        x = chain[-1]
        for i in paths_ending(D, x):
            P = orient_from(D[i], x) if (D[i][0] == x or D[i][-1] == x) else None
            # a path with both ends at x is impossible
            if w not in P:
                # finish
                try:
                    out = exec_general(D, chain, qs + [i], w)
                except AssertionError:
                    continue
                res.add(canon(out))
            else:
                j = P.index(w); z = P[j - 1]
                if z == x or z in chain:
                    continue
                rec(chain + [z], qs + [i])

    rec([t], [])
    return res


def exec_general(D, chain, idxs, w):
    """execute with the RD bookkeeping (a path may be used twice, from both ends)."""
    cur = list(D)
    k = len(chain) - 1
    for i in range(k):
        xi, xn = chain[i], chain[i + 1]
        P = cur[idxs[i]]
        assert P[0] == xi or P[-1] == xi
        Po = orient_from(P, xi)
        j = Po.index(w)
        assert Po[j - 1] == xn
        cur[idxs[i]] = tuple(reversed(Po[:j])) + Po[j:]
    P = cur[idxs[k]]
    assert P[0] == chain[k] or P[-1] == chain[k]
    Po = orient_from(P, chain[k])
    assert w not in Po
    cur[idxs[k]] = (w,) + Po
    return cur


def path_with_end(D, v):
    I = paths_ending(D, v)
    assert len(I) == 1, (v, I)
    return D[I[0]]

"""Independent implementation of Fan's addible-edge construction (Fan, JCTB 93 (2005),
Lemmas 3.3-3.4), used to replay the transfer certificates of the d6-frontier manuscript
on concrete graphs.

A decomposition is a list of vertex tuples (simple paths with >= 1 edge).  fan_add(D, u, T)
adds ONE edge t-u (t in T, t not adjacent to u in the current graph) and returns the new
decomposition together with the donor t actually used.  The construction is the chain
argument: from a donor t read a path ending at t; if it avoids u, append u; otherwise its
vertex before u is the next chain vertex; along a duplicate-free chain each path is
re-routed (reverse the segment from its end to the predecessor of u and trade that
predecessor's edge to u for the edge from the end to u), and the last path is extended by
u.  Every output is checked independently by verify()."""
from collections import deque


def edges_of(D):
    E = set()
    for P in D:
        for a, b in zip(P, P[1:]):
            e = frozenset((a, b))
            assert e not in E, "edge used twice"
            E.add(e)
    return E


def ends(D, V):
    b = {v: 0 for v in V}
    for P in D:
        b[P[0]] += 1
        b[P[-1]] += 1
    return b


def nbrs(D, v):
    s = set()
    for P in D:
        for i, w in enumerate(P):
            if w == v:
                if i > 0: s.add(P[i - 1])
                if i + 1 < len(P): s.add(P[i + 1])
    return s


def blank_nbrs(D, V, v):
    b = ends(D, V)
    return sum(1 for w in nbrs(D, v) if b[w] == 0)


def verify(D, G):
    """D is a partition of E(G) into simple paths."""
    seen = set()
    for P in D:
        if len(P) < 2 or len(set(P)) != len(P):
            return False
        for a, b in zip(P, P[1:]):
            e = frozenset((a, b))
            if not G.has_edge(a, b) or e in seen:
                return False
            seen.add(e)
    return len(seen) == G.number_of_edges()


def _oriented(P, x):
    return list(P) if P[0] == x else list(P)[::-1]


def fan_add(D, u, T):
    """Add one edge t-u, t in T, by Fan's chain construction.  Returns (D', t) or None."""
    D = [tuple(P) for P in D]
    E = edges_of(D)
    for t in T:
        assert t != u and frozenset((t, u)) not in E, "donor must be a non-neighbour"
    # BFS over chain vertices; parent[x] = (previous vertex, index of path read from it)
    parent = {}
    queue = deque()
    for t in T:
        if t not in parent:
            parent[t] = None
            queue.append(t)
    found = None
    while queue and found is None:
        x = queue.popleft()
        for i, P in enumerate(D):
            if x not in (P[0], P[-1]):
                continue
            Q = _oriented(P, x)
            if u not in Q:
                found = (x, i)
                break
            y = Q[Q.index(u) - 1]
            if y not in parent:
                parent[y] = (x, i)
                queue.append(y)
    if found is None:
        return None
    # reconstruct chain x0 (donor), ..., xk and the paths used
    xk, qi = found
    chain = [xk]
    used = []
    while parent[chain[-1]] is not None:
        px, pi = parent[chain[-1]]
        used.append((px, pi, chain[-1]))
        chain.append(px)
    chain.reverse()
    used.reverse()            # (x_i, path index, x_{i+1})
    donor = chain[0]
    D = [list(P) for P in D]
    for (xi, pi, xn) in used:
        Q = _oriented(D[pi], xi)
        j = Q.index(u)
        assert Q[j - 1] == xn
        D[pi] = Q[:j][::-1] + Q[j:]          # x_{i+1} ... x_i u ...
    Q = _oriented(D[qi], xk)
    assert u not in Q
    D[qi] = Q[::-1] + [u]                    # ... x_k u
    return [tuple(P) for P in D], donor

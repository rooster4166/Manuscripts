"""Independent audit tools for manuscripts/na (written from scratch; imports nothing from the
manuscript's scripts).

  read_g6(s)                 graph6 decoder
  verify(G, D, y, Y)         independent verifier: D partitions E(G) into paths, b(v) = d(v) mod 2,
                             Q(y) misses Y, every path meets Y at most once.  Returns (ok, reason).
  all_lovasz(G)              every Lovasz decomposition of a small graph with no even vertex, by an
                             edge-driven recursion (the path containing the least uncovered edge is
                             grown in both directions); a different algorithm from exact.py.
  good(G, y, Y, meets_once)  exists a Lovasz decomposition with Q(y) n Y empty (and, if meets_once,
                             every path meeting Y at most once)?  Memoised edge-driven search.
"""
from functools import lru_cache


def read_g6(s):
    s = s.strip()
    v = [ord(c) - 63 for c in s]
    n, v = v[0], v[1:]
    assert n < 63
    bits = []
    for d in v:
        bits.extend((d >> k) & 1 for k in range(5, -1, -1))
    G = {i: set() for i in range(n)}
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                G[i].add(j)
                G[j].add(i)
            k += 1
    return G


def edge(a, b):
    return (a, b) if repr(a) <= repr(b) else (b, a)


def verify(G, D, y=None, Y=()):
    Y = set(Y)
    used = set()
    ends = {}
    for P in D:
        if len(P) < 2:
            return False, "trivial path"
        if len(set(P)) != len(P):
            return False, "repeated vertex"
        for a, b in zip(P, P[1:]):
            if b not in G.get(a, ()):
                return False, "not an edge"
            e = edge(a, b)
            if e in used:
                return False, "edge twice"
            used.add(e)
        for v in (P[0], P[-1]):
            ends[v] = ends.get(v, 0) + 1
    E = {edge(a, b) for a in G for b in G[a]}
    if used != E:
        return False, "not a partition of E"
    for v in set(G) | set(ends):
        if ends.get(v, 0) != len(G.get(v, ())) % 2:
            return False, "wrong number of ends at %r" % (v,)
    if y is not None:
        Qs = [P for P in D if y in (P[0], P[-1])]
        if len(Qs) != 1:
            return False, "Q(y) not unique"
        if set(Qs[0]) & Y:
            return False, "Q(y) meets Y"
    for P in D:
        if len(set(P) & Y) > 1:
            return False, "path meets Y twice"
    return True, ""


def _adj(E):
    A = {}
    for a, b in E:
        A.setdefault(a, set()).add(b)
        A.setdefault(b, set()).add(a)
    return A


def _paths_through(E, A, a, b):
    """All simple paths using edge ab within edge set E, as vertex lists, whose two ends have odd
    degree in E (they must be ends of the path) -- interior vertices are unconstrained here."""
    odd = {v for v in A if len(A[v]) % 2 == 1}
    out = []

    def grow(P, usedv):
        # extend at the right end only; P[-1] is the current right end
        yield P
        cur = P[-1]
        for c in A[cur]:
            if c not in usedv:
                usedv.add(c)
                yield from grow(P + [c], usedv)
                usedv.remove(c)

    for left in grow([a], {a, b}):
        # left = a ... (growing away from b); now grow right from b avoiding left
        L = left[::-1]  # ... a
        usedv = set(L) | {b}
        for right in grow([b], usedv):
            P = L + right
            if P[0] in odd and P[-1] in odd:
                out.append(P)
    return out


def all_lovasz(G):
    """All Lovasz decompositions (G with no even vertex), as frozensets of tuples."""
    E0 = frozenset(edge(a, b) for a in G for b in G[a])
    res = []

    def rec(E, acc):
        if not E:
            res.append(list(acc))
            return
        A = _adj(E)
        if not any(len(A[v]) % 2 for v in A):
            return
        a, b = min(E, key=repr)
        for P in _paths_through(E, A, a, b):
            PE = {edge(p, q) for p, q in zip(P, P[1:])}
            acc.append(P)
            rec(E - PE, acc)
            acc.pop()

    rec(E0, [])
    # canonical dedupe
    seen = set()
    out = []
    for D in res:
        key = frozenset(tuple(P) if repr(P[0]) <= repr(P[-1]) else tuple(P[::-1]) for P in D)
        if key not in seen:
            seen.add(key)
            out.append(D)
    return out


def good(G, y, Y, meets_once=False):
    """Some Lovasz decomposition with Q(y) n Y empty (and every path meeting Y <= once if asked)."""
    Y = frozenset(Y)
    E0 = frozenset(edge(a, b) for a in G for b in G[a])

    @lru_cache(maxsize=None)
    def rec(E, ydone):
        if not E:
            return ydone
        A = _adj(E)
        if not any(len(A[v]) % 2 for v in A):
            return False
        a, b = min(E, key=repr)
        for P in _paths_through(E, A, a, b):
            if meets_once and len(set(P) & Y) > 1:
                continue
            isQ = y in (P[0], P[-1])
            if isQ and set(P) & Y:
                continue
            PE = frozenset(edge(p, q) for p, q in zip(P, P[1:]))
            if rec(E - PE, ydone or isQ):
                return True
        return False

    return rec(E0, False)


def component(G, s, banned):
    seen = {s}
    st = [s]
    while st:
        a = st.pop()
        for c in G[a]:
            if c not in banned and c not in seen:
                seen.add(c)
                st.append(c)
    return seen


def weak(G, y, Y):
    """The component of y in G - Y has a vertex outside N(Y)."""
    NY = set()
    for a in Y:
        NY |= G[a]
    return any(v not in NY for v in component(G, y, set(Y)))


def packed(G, Y):
    Y = list(Y)
    for i in range(len(Y)):
        for j in range(i + 1, len(Y)):
            a, b = Y[i], Y[j]
            if b in G[a] or (G[a] & G[b]):
                return False
    return True

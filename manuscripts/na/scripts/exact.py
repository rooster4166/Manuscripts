"""Exact decision procedures, independent of nalib's construction.

  decomposable(E)     : does the edge set E split into paths with every vertex an end of exactly
                        d_E(v) mod 2 of them?  (DFS over paths from the least odd vertex, memoised.)
  avoid_exact(G,y,X)  : is there a Lovasz decomposition of G whose path ending at y avoids X?
  brute_all(G)        : all Lovasz decompositions of a small graph, by enumerating transition systems
                        (pairings of the edges at every vertex), used to validate the two above.
"""
from functools import lru_cache
from itertools import combinations


def _adj(E):
    A = {}
    for e in E:
        a, b = tuple(e)
        A.setdefault(a, set()).add(b)
        A.setdefault(b, set()).add(a)
    return A


@lru_cache(maxsize=None)
def decomposable(E):
    """E: frozenset of frozenset edges."""
    if not E:
        return True
    A = _adj(E)
    odd = sorted(v for v in A if len(A[v]) % 2 == 1)
    if not odd:
        return False  # a non-empty graph with all degrees even has no path decomposition with no ends
    # pruning: a component with p ends-pairs and n_C vertices has at most p(n_C - 1) edges
    v = odd[0]
    oddset = set(odd)
    # enumerate paths from v ending at another odd vertex
    stack = [(v, [v], frozenset())]
    while stack:
        cur, P, used = stack.pop()
        for c in A[cur]:
            e = frozenset((cur, c))
            if e in used or c in P:
                continue
            nu = used | {e}
            if c in oddset:
                if decomposable(E - nu):
                    return True
            stack.append((c, P + [c], nu))
    return False


def avoid_exact(G, y, X):
    """Some Lovasz decomposition of G (all degrees odd or zero except possibly one even vertex)
    has its path ending at y disjoint from X?  Returns the path Q(y) found, or None."""
    X = set(X)
    E = frozenset(frozenset((a, b)) for a in G for b in G[a])
    oddv = set(v for v in G if len(G[v]) % 2 == 1)
    assert y in oddv
    stack = [(y, [y], frozenset())]
    while stack:
        cur, P, used = stack.pop()
        for c in G[cur]:
            e = frozenset((cur, c))
            if c in P or c in X:
                continue
            nu = used | {e}
            if c in oddv and decomposable(E - nu):
                return P + [c]
            stack.append((c, P + [c], nu))
    return None


def brute_all(G, cap=2_000_000):
    """All Lovasz decompositions (as sorted tuples of paths) via transition systems."""
    V = sorted(G)
    choices = []
    for v in V:
        nb = sorted(G[v])
        # pairings of the incident edges with d(v) mod 2 singletons
        opts = []

        def rec(rest, pairs):
            if len(rest) <= (len(nb) % 2):
                opts.append(tuple(pairs))
                return
            a = rest[0]
            if len(rest) % 2 == 1 and len(nb) % 2 == 1:
                # a may be the singleton
                rec(rest[1:], pairs)
            for b in rest[1:]:
                r2 = [z for z in rest[1:] if z != b]
                rec(r2, pairs + [(a, b)])

        rec(nb, [])
        choices.append(opts)
    out = set()
    count = [0]

    def build(i, sel):
        if count[0] > cap:
            raise RuntimeError("cap")
        if i == len(V):
            count[0] += 1
            # follow trails
            nxt = {}
            for v, pairs in zip(V, sel):
                for a, b in pairs:
                    nxt[(v, a)] = b
                    nxt[(v, b)] = a
            usedE = set()
            paths = []
            for v in V:
                for a in G[v]:
                    if (v, a) in nxt:
                        continue
                    e = frozenset((v, a))
                    if e in usedE:
                        continue
                    # v is an end with edge va
                    P = [v]
                    prev, cur = v, a
                    usedE.add(e)
                    P.append(cur)
                    while (cur, prev) in nxt:
                        n2 = nxt[(cur, prev)]
                        usedE.add(frozenset((cur, n2)))
                        prev, cur = cur, n2
                        P.append(cur)
                    paths.append(P)
            if len(usedE) != sum(len(G[v]) for v in V) // 2:
                return  # closed trails remain
            for P in paths:
                if len(set(P)) != len(P):
                    return
            key = tuple(sorted(tuple(P) if P[0] < P[-1] else tuple(P[::-1]) for P in paths))
            out.add(key)
            return
        for o in choices[i]:
            build(i + 1, sel + [o])

    build(0, [])
    return out

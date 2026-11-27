"""bf.py (audit A22): independent brute-force search for constrained Lovasz decompositions.

Written from scratch for the audit (shares no code with scripts/ptm.c or walk.c).

A Lovasz decomposition of K with end profile b (b(v) in {0,1}, b(v) = d(v) mod 2) is built path by
path: pick an unfinished vertex v (b(v) = 1, not yet an end), enumerate every simple path from v in
the remaining edges that ends at another unfinished vertex, delete it, recurse.  Every Lovasz
decomposition is found this way (v's own path is enumerated from v), so the search is exhaustive.
Failed states (remaining edges, finished vertices) are memoised; the state determines the rest of
the problem because all constraints are local to single paths.

Constraints supported:
  first[v] = w : the path ending at v has terminal edge vw   (v is processed first, path starts vw)
  noends      : set of frozenset pairs {s, s'} that may not be the two ends of one path
  sep         : list of pairs (p, q): no path contains both p and q
"""
import sys
from functools import lru_cache


def parse_g6(s):
    s = s.strip()
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        k = ord(ch) - 63
        for i in range(5, -1, -1):
            bits.append((k >> i) & 1)
    A = [[0] * n for _ in range(n)]
    t = 0
    for j in range(1, n):
        for i in range(j):
            if bits[t]:
                A[i][j] = A[j][i] = 1
            t += 1
    return n, A


class Search:
    def __init__(self, n, edges, prof, first=None, noends=(), sep=()):
        self.n = n
        self.edges = edges
        self.adj = [[] for _ in range(n)]
        for e, (u, v) in enumerate(edges):
            self.adj[u].append((v, e))
            self.adj[v].append((u, e))
        self.prof = prof                      # target number of ends (0/1)
        self.first = dict(first or {})        # v -> w
        self.noends = set(noends)
        self.sepmate = [0] * n                # bitmask of vertices separated from v
        for p, q in sep:
            self.sepmate[p] |= 1 << q
            self.sepmate[q] |= 1 << p
        self.order_first = list(self.first)   # constrained vertices first
        self.memo = set()
        self.solution = None

    def deg(self, v, rem):
        return sum(1 for (w, e) in self.adj[v] if rem >> e & 1)

    def comps_ok(self, rem, todo):
        # degree bound: with P paths left, v lies on at most P of them, using <= 2 edges on each
        # and only 1 on the path ending at v (if v still needs an end)
        P = bin(todo).count('1') // 2
        for v in range(self.n):
            if self.deg(v, rem) > 2 * P - (todo >> v & 1):
                return False
        seen = 0
        for v in range(self.n):
            if seen >> v & 1:
                continue
            if self.deg(v, rem) == 0:
                continue
            comp = 1 << v
            st = [v]
            while st:
                x = st.pop()
                for (w, e) in self.adj[x]:
                    if rem >> e & 1 and not comp >> w & 1:
                        comp |= 1 << w
                        st.append(w)
            seen |= comp
            c = bin(comp & todo).count('1')
            if c < 2:
                return False
        return True

    def solve(self, rem, todo, paths):
        if rem == 0:
            if todo == 0:
                self.solution = list(paths)
                return True
            return False
        if todo == 0:
            return False
        key = (rem, todo)
        if key in self.memo:
            return False
        if not self.comps_ok(rem, todo):
            self.memo.add(key)
            return False
        # choose start vertex
        v = None
        for s in self.order_first:
            if todo >> s & 1:
                v = s
                break
        if v is None:
            best = None
            for u in range(self.n):
                if todo >> u & 1:
                    d = self.deg(u, rem)
                    if best is None or d < best:
                        best, v = d, u
        res = self.grow(v, v, 1 << v, rem, todo, [v], paths)
        if not res:
            self.memo.add(key)
        return res

    def grow(self, v, c, vis, rem, todo, path, paths):
        for (w, e) in self.adj[c]:
            if not rem >> e & 1 or vis >> w & 1:
                continue
            if self.sepmate[w] & vis:
                continue
            if c == v and v in self.first and w != self.first[v]:
                continue
            rem2 = rem & ~(1 << e)
            path.append(w)
            # close at w?
            if todo >> w & 1 and frozenset((v, w)) not in self.noends:
                ok_end = True
                if w in self.first and self.first[w] != c:
                    ok_end = False
                if ok_end:
                    paths.append(tuple(path))
                    if self.solve(rem2, todo & ~(1 << v) & ~(1 << w), paths):
                        return True
                    paths.pop()
            # continue through w
            if any(rem2 >> e2 & 1 for (_, e2) in self.adj[w]):
                if self.grow(v, w, vis | 1 << w, rem2, todo, path, paths):
                    return True
            path.pop()
        return False

    def run(self):
        rem = (1 << len(self.edges)) - 1
        todo = 0
        for v in range(self.n):
            if self.prof[v]:
                todo |= 1 << v
        return self.solve(rem, todo, [])


def verify(n, edges, prof, paths, first, noends, sep):
    """Independent check of a witness."""
    used = set()
    ends = [0] * n
    E = {frozenset(e) for e in edges}
    for P in paths:
        if len(P) < 2 or len(set(P)) != len(P):
            return False
        for i in range(len(P) - 1):
            f = frozenset((P[i], P[i + 1]))
            if f not in E or f in used:
                return False
            used.add(f)
        ends[P[0]] += 1
        ends[P[-1]] += 1
        if frozenset((P[0], P[-1])) in noends:
            return False
        for p, q in sep:
            if p in P and q in P:
                return False
        for (s, t) in ((P[0], P[1]), (P[-1], P[-2])):
            if s in first and first[s] != t:
                return False
    return used == E and all(ends[v] == prof[v] for v in range(n))


def lovasz(n, A, first=None, noends=(), sep=()):
    edges = [(u, v) for u in range(n) for v in range(u + 1, n) if A[u][v]]
    prof = [sum(A[v]) % 2 for v in range(n)]
    S = Search(n, edges, prof, first, noends, sep)
    ok = S.run()
    if ok:
        assert verify(n, edges, prof, S.solution, first or {}, set(noends), sep), 'bad witness'
    return ok, S.solution


def ptm_assign(n, A, F, shorts):
    """Lovasz decomposition of G (adjacency A, F-edges included) with F[i] terminal at shorts[i]
    and no two F-edges on one path."""
    first = {}
    for (u, v), s in zip(F, shorts):
        first[s] = v if s == u else u
    noends = {frozenset((s, t)) for i, s in enumerate(shorts) for t in shorts[i + 1:]}
    return lovasz(n, A, first, noends)[0]


class SearchE(Search):
    """Multigraph variant: first_e[v] = edge id of the required terminal edge at v."""
    def __init__(self, n, edges, prof, first_e, noends=()):
        super().__init__(n, edges, prof, None, noends, ())
        self.first_e = dict(first_e)
        self.order_first = list(self.first_e)

    def grow(self, v, c, vis, rem, todo, path, paths):
        for (w, e) in self.adj[c]:
            if not rem >> e & 1 or vis >> w & 1:
                continue
            if c == v and v in self.first_e and e != self.first_e[v]:
                continue
            rem2 = rem & ~(1 << e)
            path.append(w)
            if todo >> w & 1 and frozenset((v, w)) not in self.noends:
                if not (w in self.first_e and self.first_e[w] != e):
                    paths.append((tuple(path), e))
                    if self.solve(rem2, todo & ~(1 << v) & ~(1 << w), paths):
                        return True
                    paths.pop()
            if any(rem2 >> e2 & 1 for (_, e2) in self.adj[w]):
                if self.grow(v, w, vis | 1 << w, rem2, todo, path, paths):
                    return True
            path.pop()
        return False


def ptm_multi(n, Gp_edges, F, shorts):
    """G = G' + F as a multigraph (an F-edge may be parallel to a G'-edge); F[i] terminal at
    shorts[i] (the F-edge itself, not a parallel copy), no two F-edges on one path."""
    edges = list(Gp_edges) + list(F)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    prof = [d % 2 for d in deg]
    first_e = {s: len(Gp_edges) + i for i, s in enumerate(shorts)}
    noends = {frozenset((s, t)) for i, s in enumerate(shorts) for t in shorts[i + 1:]}
    S = SearchE(n, edges, prof, first_e, noends)
    return S.run()

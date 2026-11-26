"""Independent solver for the Fan game of missing-move Definition 1.1 (audit A12).

Written for the audit; it shares no code with manuscripts/missing-move/scripts/fan_game.py.

State: (held, b), where held is a bitmask over the edge list of G and b is the profile (a tuple of
end counts). The current graph is H = G - held. Moves (missing-move Def 1.1, Section 1 "Results"):
  * single transfer of a held edge tu towards u, if b(t) > |Z_H(u)|;
  * grouped transfer at u with a set T (|T| >= 2) of held edges tu, if sum_T b > |Z_H(u)|;
    the opponent chooses the donor t in T with b(t) >= 1 (AND over donors);
  * new one-edge path: held edge ac, b(a) += 1, b(c) += 1;
  * [newpath] new path of length >= 2 made of held edges: b += 1 at both ends.
Terminal (no held edge): win for r iff sum b <= n and b(r) >= 1; with split=True also when
sum b <= n - 2 (the split rule).
Seeds on K = G - F: Lovasz (at most one vertex of positive even degree): b = d_K mod 2;
"Lemma 3/4" seed (K has no isolated vertex and exactly two even vertices u, v): b = 1 on odd
vertices, b(v) = 2, b(u) = 0.

The value of a state is the bitmask of roots r for which the player wins from it (exact; no
short-cut except when the mask is already full), so one search serves every root.
"""
import sys
from itertools import combinations


class Game:
    def __init__(self, n, edges, newpath=True, split=False, flower=False):
        self.n = n
        self.E = sorted(tuple(sorted(e)) for e in edges)
        self.m = len(self.E)
        self.eid = {e: i for i, e in enumerate(self.E)}
        self.inc = [[] for _ in range(n)]          # edge ids at each vertex
        for i, (a, c) in enumerate(self.E):
            self.inc[a].append(i)
            self.inc[c].append(i)
        self.other = {}
        for i, (a, c) in enumerate(self.E):
            self.other[(i, a)] = c
            self.other[(i, c)] = a
        self.newpath = newpath
        self.split = split
        self.full = (1 << n) - 1
        self.memo = {}

    # ------------------------------------------------------------------
    def blanks(self, held, b, u):
        z = 0
        for i in self.inc[u]:
            if not (held >> i) & 1:
                if b[self.other[(i, u)]] == 0:
                    z += 1
        return z

    def terminal(self, b):
        s = sum(b)
        if s > self.n:
            return 0
        if self.split and s <= self.n - 2:
            return self.full
        mk = 0
        for v in range(self.n):
            if b[v] >= 1:
                mk |= 1 << v
        return mk

    def children(self, held, b):
        """Yield lists of child states; the player picks a list, the opponent a child in it."""
        n = self.n
        s = sum(b)
        hl = [i for i in range(self.m) if (held >> i) & 1]
        # single transfers and new one-edge paths
        for i in hl:
            a, c = self.E[i]
            h2 = held & ~(1 << i)
            for u, t in ((a, c), (c, a)):
                if b[t] > self.blanks(held, b, u):
                    nb = list(b); nb[u] += 1; nb[t] -= 1
                    yield [(h2, tuple(nb))]
            if s + 2 <= n:
                nb = list(b); nb[a] += 1; nb[c] += 1
                yield [(h2, tuple(nb))]
        # new paths of length >= 2 in the held graph
        if self.newpath and s + 2 <= n:
            hadj = {}
            for i in hl:
                a, c = self.E[i]
                hadj.setdefault(a, []).append((c, i))
                hadj.setdefault(c, []).append((a, i))
            out = []

            def ext(path, used):
                if len(path) >= 3 and path[0] < path[-1]:
                    nb = list(b); nb[path[0]] += 1; nb[path[-1]] += 1
                    out.append((held & ~used, tuple(nb)))
                for w, i in hadj.get(path[-1], ()):
                    if w not in path:
                        ext(path + [w], used | (1 << i))

            for v in hadj:
                ext([v], 0)
            for st in out:
                yield [st]
        # grouped transfers
        for u in range(n):
            hu = [i for i in self.inc[u] if (held >> i) & 1]
            if len(hu) < 2:
                continue
            z = self.blanks(held, b, u)
            for k in range(2, len(hu) + 1):
                for T in combinations(hu, k):
                    ts = [self.other[(i, u)] for i in T]
                    if sum(b[t] for t in ts) <= z:
                        continue
                    br = []
                    for i, t in zip(T, ts):
                        if b[t] >= 1:
                            nb = list(b); nb[u] += 1; nb[t] -= 1
                            br.append((held & ~(1 << i), tuple(nb)))
                    yield br

    def value(self, held, b):
        key = (held, b)
        v = self.memo.get(key)
        if v is not None:
            return v
        if sum(b) > self.n:
            self.memo[key] = 0
            return 0
        if held == 0:
            v = self.terminal(b)
            self.memo[key] = v
            return v
        acc = 0
        for br in self.children(held, b):
            w = self.full
            for st in br:
                w &= self.value(*st)
                if w == 0 or (w | acc) == acc:
                    break
            acc |= w
            if acc == self.full:
                break
        # NB: the early breaks inside a branch list only skip work that cannot enlarge acc,
        # but they make w an under-approximation; acc stays exact because a skipped branch can
        # only shrink w further, and w | acc == acc means w adds nothing.
        self.memo[key] = acc
        return acc

    # ------------------------------------------------------------------
    def seeds(self, F):
        n = self.n
        deg = [0] * n
        Fs = 0
        for i in F:
            Fs |= 1 << i
        for i, (a, c) in enumerate(self.E):
            if not (Fs >> i) & 1:
                deg[a] += 1; deg[c] += 1
        pe = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
        out = []
        if len(pe) <= 1:
            out.append(("lovasz", tuple(d % 2 for d in deg)))
        if all(d > 0 for d in deg) and len(pe) == 2:
            for u, v in (pe, pe[::-1]):
                bb = [d % 2 for d in deg]; bb[v] = 2; bb[u] = 0
                out.append(("lemma4", tuple(bb)))
        return Fs, out

    def solve(self, kmax, kmin=0, roots=None, heldsets=None):
        """Least |F| (kmin..kmax) at which each root wins; returns {r: (k, F, seed) or None}."""
        want = self.full if roots is None else sum(1 << r for r in roots)
        best = {}
        got = 0
        for k in range(kmin, kmax + 1):
            gen = heldsets(k) if heldsets else combinations(range(self.m), k)
            newly = 0
            for F in gen:
                Fs, sd = self.seeds(F)
                for kind, b0 in sd:
                    v = self.value(Fs, b0) & want & ~got
                    if v:
                        for r in range(self.n):
                            if (v >> r) & 1 and r not in best:
                                best[r] = (k, tuple(self.E[i] for i in F), kind, b0)
                        newly |= v
                        got |= v
                if got == want:
                    break
            if got == want:
                break
        return {r: best.get(r) for r in range(self.n) if (want >> r) & 1}


def from_g6(g6):
    import networkx as nx
    G = nx.from_graph6_bytes(g6.encode() if isinstance(g6, str) else g6)
    return G.number_of_nodes(), [tuple(e) for e in G.edges()]


if __name__ == "__main__":
    g6, kmax = sys.argv[1], int(sys.argv[2])
    opts = sys.argv[3:]
    n, E = from_g6(g6)
    gm = Game(n, E, newpath="nonp" not in opts, split="split" in opts)
    res = gm.solve(kmax)
    for r, v in res.items():
        print(r, v)

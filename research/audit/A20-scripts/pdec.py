"""A20 independent checker: exhaustive search for path decompositions with a prescribed end
profile and constraints at a vertex z.  Written from scratch for audit A20; it shares no code with
tools/stl.c or manuscripts/stl/scripts/*.

Search: always start the next path at the smallest vertex with remaining end budget, enumerate
every simple path from it through unused edges that stops at another vertex with remaining budget,
recurse.  This is complete: in any decomposition with the profile, the smallest vertex with
remaining budget is an end of some not-yet-placed path, and that path can be placed next, read from
that vertex.  Failures are memoised on (used-edge mask, remaining budgets, accumulator), which is
exact because the accumulator is all the future depends on.

A path through z (z never an end here) has its two neighbours a (before z) and b (after z); the
side at a is short iff a is the first vertex, at b iff b is the last vertex.  `step(acc, info)`
updates the accumulator or returns None (path forbidden); `final(acc)` decides success.
"""
import sys
import networkx as nx

sys.setrecursionlimit(10000)


class Graph:
    def __init__(self, G):
        nodes = sorted(G.nodes())
        self.lab = {v: i for i, v in enumerate(nodes)}
        self.n = len(nodes)
        self.E = []
        self.adj = [[] for _ in range(self.n)]
        for (u, v) in G.edges():
            a, b = self.lab[u], self.lab[v]
            i = len(self.E)
            self.E.append((a, b))
            self.adj[a].append((b, i))
            self.adj[b].append((a, i))
        self.deg = [len(x) for x in self.adj]
        self.m = len(self.E)


def search(g, prof, z=None, star=False, step=None, final=None, acc0=None, witness=False,
           maxpaths=None):
    """Is there a decomposition of g with b(v) = prof[v] for all v, every path through z
    star-terminal if `star`, path-level constraint `step`, global `final`?"""
    n, m = g.n, g.m
    if any(prof[v] > g.deg[v] or (g.deg[v] - prof[v]) % 2 for v in range(n)):
        return None if witness else False
    if sum(prof) % 2:
        return None if witness else False
    if z is not None and prof[z] != 0:
        raise ValueError("z must not be an end")
    full = (1 << m) - 1
    fail = set()
    budget = list(prof)
    rem = list(g.deg)
    sol = []

    def ok_vertex(v):
        return rem[v] >= budget[v] and (rem[v] - budget[v]) % 2 == 0

    def info_of(path):
        if z is None or z not in path:
            return None
        i = path.index(z)
        a, b = path[i - 1], path[i + 1]
        return (a, i - 1 == 0, b, i + 1 == len(path) - 1)

    def comp_ok(used):
        # every component of the unused edges needs an even, positive end budget
        par = list(range(n))

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        for i, (a, b) in enumerate(g.E):
            if not (used >> i) & 1:
                ra, rb = find(a), find(b)
                if ra != rb:
                    par[ra] = rb
        tot = {}
        for v in range(n):
            if rem[v] > 0 or budget[v] > 0:
                r_ = find(v)
                tot[r_] = tot.get(r_, 0) + budget[v]
        return all(t >= 2 and t % 2 == 0 for t in tot.values())

    def rec(used, acc):
        key = (used, tuple(budget), acc)
        if key in fail:
            return False
        if used != full and not comp_ok(used):
            fail.add(key)
            return False
        cands = [v for v in range(n) if budget[v] > 0]
        v0 = min(cands, key=lambda v: (rem[v], v)) if cands else None
        if v0 is None:
            res = used == full and (final is None or final(acc))
            if not res:
                fail.add(key)
            return res
        # enumerate simple paths from v0
        path = [v0]
        onpath = [False] * n
        onpath[v0] = True
        budget[v0] -= 1
        found = [False]

        def ext(cur, used_p, zi):
            # option: stop at cur
            if cur != v0 and budget[cur] > 0:
                budget[cur] -= 1
                inf = info_of(path)
                nacc = acc
                okp = True
                if step is not None:
                    nacc = step(acc, inf, path)
                    okp = nacc is not None
                if okp:
                    vs = set(path)
                    if all(ok_vertex(x) for x in vs):
                        sol.append(list(path))
                        if rec(used_p, nacc):
                            found[0] = True
                            budget[cur] += 1
                            return True
                        sol.pop()
                budget[cur] += 1
            # option: extend
            if star and zi is not None and zi >= 2 and len(path) - 1 >= zi + 1:
                return False  # z is not second, so the vertex after z must be the end
            for (w, e) in g.adj[cur]:
                if onpath[w] or (used_p >> e) & 1:
                    continue
                if w == z and zi is None and star is False:
                    pass
                onpath[w] = True
                path.append(w)
                rem[cur] -= 1
                rem[w] -= 1
                nzi = zi
                if w == z:
                    nzi = len(path) - 1
                if ext(w, used_p | (1 << e), nzi):
                    return True
                rem[cur] += 1
                rem[w] += 1
                path.pop()
                onpath[w] = False
            return False

        r = ext(v0, used, 0 if v0 == z else None)
        budget[v0] += 1
        if r:
            return True
        fail.add(key)
        return False

    res = rec(0, acc0)
    if witness:
        return [list(p) for p in sol] if res else None
    return res


# ---------------------------------------------------------------- queries

def lovasz_prof(g):
    return [d % 2 for d in g.deg]


def st(g, z):
    """some star-terminal Lovasz decomposition"""
    return search(g, lovasz_prof(g), z=z, star=True)


def stl(g, z, r, witness=False):
    """star-terminal Lovasz decomposition with r long or some SS transition"""
    def step(acc, inf, path):
        rl, ss = acc
        if inf is None:
            return acc
        a, sa, b, sb = inf
        if not sa and not sb:
            return None
        if sa and sb:
            ss = True
        if (a == r and not sa) or (b == r and not sb):
            rl = True
        return (rl, ss)
    return search(g, lovasz_prof(g), z=z, star=True, step=step, final=lambda acc: acc[0] or acc[1],
                  acc0=(False, False), witness=witness)


def bal(g, z, r, prof=None):
    """decomposition with profile prof (default Lovasz), #LL - #SS + [r short] <= 0"""
    prof = prof or lovasz_prof(g)
    def step(acc, inf, path):
        val, rs = acc
        if inf is None:
            return acc
        a, sa, b, sb = inf
        if not sa and not sb:
            val += 1
        if sa and sb:
            val -= 1
        if (a == r and sa) or (b == r and sb):
            rs = 1
        return (val, rs)
    return search(g, prof, z=z, star=False, step=step, final=lambda acc: acc[0] + acc[1] <= 0,
                  acc0=(0, 0))


def pairing(g, z, M, witness=False):
    """star-terminal Lovasz decomposition whose transitions at z are exactly M (set of frozensets)"""
    def step(acc, inf, path):
        if inf is None:
            return acc
        a, sa, b, sb = inf
        if frozenset((a, b)) not in M:
            return None
        return acc
    return search(g, lovasz_prof(g), z=z, star=True, step=step, acc0=0, witness=witness)


def short_at(g, z, u, star):
    """Lovasz decomposition (star-terminal if star) in which u is short (uz terminal at u)"""
    def step(acc, inf, path):
        if inf is None:
            return acc
        a, sa, b, sb = inf
        if (a == u and sa) or (b == u and sb):
            return True
        return acc
    return search(g, lovasz_prof(g), z=z, star=star, step=step, final=lambda acc: acc, acc0=False)


def stl2(g, z, r):
    """STL2: b(z)=0, b(r) in {0,2}, b(v)=d(v) mod 2 else; star-terminal; b(r)=0 or r long or SS"""
    for beta in (0, 2):
        prof = lovasz_prof(g)
        prof[r] = beta
        def step(acc, inf, path):
            rl, ss = acc
            if inf is None:
                return acc
            a, sa, b, sb = inf
            if not sa and not sb:
                return None
            if sa and sb:
                ss = True
            if (a == r and not sa) or (b == r and not sb):
                rl = True
            return (rl, ss)
        fin = (lambda acc: True) if beta == 0 else (lambda acc: acc[0] or acc[1])
        if search(g, prof, z=z, star=True, step=step, final=fin, acc0=(False, False)):
            return True
    return False


def profiles(gh, sumb, lower):
    """all profiles b on gh with parity of degree, lower[v] <= b[v] <= deg, sum = sumb"""
    n = gh.n
    base = [max(lower[v], gh.deg[v] % 2) for v in range(n)]
    for v in range(n):
        if (base[v] - gh.deg[v]) % 2:
            base[v] += 1
    extra = sumb - sum(base)
    if extra < 0 or extra % 2:
        return
    out = []

    def rec(i, left, b):
        if i == n:
            if left == 0:
                out.append(list(b))
            return
        k = 0
        while base[i] + 2 * k <= gh.deg[i] and 2 * k <= left:
            b.append(base[i] + 2 * k)
            rec(i + 1, left - 2 * k, b)
            b.pop()
            k += 1
    rec(0, extra, [])
    for b in out:
        if all(b[v] <= gh.deg[v] for v in range(n)):
            yield b


def delete(G, z):
    H = G.copy()
    H.remove_node(z)
    return H


def test_k_ends(G, z, r, maxpaths, kends):
    """J - z has a decomposition into <= maxpaths paths with >= kends ends at r.
    Splitting at an interior visit adds one path and two ends at that vertex and keeps the rest,
    so it suffices to test sum b = 2*maxpaths exactly when 2*maxpaths <= 2m (parity permitting),
    and the all-single-edges decomposition otherwise."""
    H = delete(G, z)
    gh = Graph(H)
    rr = gh.lab[r]
    if gh.deg[rr] < kends:
        return False
    if gh.m <= maxpaths:
        return True  # single edges: b(r) = deg(r) >= kends
    target = 2 * maxpaths
    lower = [0] * gh.n
    lower[rr] = kends
    # parity of the target sum: sum b = sum of degrees mod 2 = 0, and target is even
    for b in profiles(gh, target, lower):
        if search(gh, b):
            return True
    # target might be unreachable by parity of individual lower bounds; try target-2, etc.
    # (cannot happen: lifting by splits changes the sum by 2, so if any realisable profile of
    # smaller even sum exists, one of sum = target exists)
    return False


def test1(G, z, r):
    n = G.number_of_nodes()
    return test_k_ends(G, z, r, (n - 1) // 2, 2)


def test2(G, z, r):
    n = G.number_of_nodes()
    return test_k_ends(G, z, r, n // 2, 3)


def perfect_matchings(S):
    S = list(S)
    if not S:
        yield []
        return
    a = S[0]
    for i in range(1, len(S)):
        rest = S[1:i] + S[i + 1:]
        for M in perfect_matchings(rest):
            yield [frozenset((a, S[i]))] + M

"""A20: check Proposition 4.1 (STL seen from J - z) against the direct definition of STL,
on all one-even graphs of order 5 and 7, every r in N(z).

Direct side: pdec.stl.  J - z side: enumerate every decomposition D' of J - z with b'(v) = 1 off
N[z] and b'(w) in {0, 2} on N(z), T = {b' = 2}, |T| <= k, (r in T or |T| < k); then look for a
perfect matching sigma of N(z) matching T into N(z) - T and distinct paths B_y (y in T) ending at
y with sigma(y) not on B_y.
"""
import itertools
import networkx as nx
from pdec import Graph, stl, perfect_matchings

SCR = '/home/user/Manuscripts/manuscripts/stl/scripts/'


def all_decomps(g, prof):
    """yield every decomposition (list of vertex lists) of g with end profile prof"""
    n, m = g.n, g.m
    full = (1 << m) - 1
    budget = list(prof)
    sol = []

    def rec(used):
        v0 = next((v for v in range(n) if budget[v] > 0), None)
        if v0 is None:
            if used == full:
                yield [list(p) for p in sol]
            return
        budget[v0] -= 1
        path = [v0]
        on = [False] * n
        on[v0] = True

        def ext(cur, u):
            if cur != v0 and budget[cur] > 0:
                budget[cur] -= 1
                sol.append(list(path))
                yield from rec(u)
                sol.pop()
                budget[cur] += 1
            for (w, e) in g.adj[cur]:
                if on[w] or (u >> e) & 1:
                    continue
                on[w] = True
                path.append(w)
                yield from ext(w, u | (1 << e))
                path.pop()
                on[w] = False
        yield from ext(v0, used)
        budget[v0] += 1
    yield from rec(0)


def jz_side(J, z, r):
    H = J.copy(); H.remove_node(z)
    gh = Graph(H)
    N = [gh.lab[w] for w in J[z]]
    rr = gh.lab[r]
    k = len(N) // 2
    for t in range(0, k + 1):
        for T in itertools.combinations(N, t):
            if not (rr in T or t < k):
                continue
            prof = [1] * gh.n
            for w in N:
                prof[w] = 2 if w in T else 0
            if any(prof[v] > gh.deg[v] or (gh.deg[v] - prof[v]) % 2 for v in range(gh.n)):
                continue
            Tset = set(T)
            for Dp in all_decomps(gh, prof):
                for sig in perfect_matchings(N):
                    # sigma must match T into N - T
                    sd = {}
                    okm = True
                    for p in sig:
                        a, b = tuple(p)
                        if a in Tset and b in Tset:
                            okm = False
                        sd[a] = b; sd[b] = a
                    if not okm:
                        continue
                    # distinct B_y: bipartite assignment by brute force
                    cand = {y: [i for i, P in enumerate(Dp)
                                if (P[0] == y or P[-1] == y) and sd[y] not in P] for y in T}
                    def assign(ys, used):
                        if not ys:
                            return True
                        y = ys[0]
                        return any(assign(ys[1:], used | {i}) for i in cand[y] if i not in used)
                    if assign(list(T), frozenset()):
                        return True
    return False


for n in (5, 7):
    agree = dis = 0
    for l in open(SCR + 'one_even_%d.g6' % n, 'rb'):
        J = nx.from_graph6_bytes(l.strip())
        ev = [v for v in J if J.degree(v) % 2 == 0]
        if len(ev) != 1 or J.degree(ev[0]) == 0:
            continue
        z = ev[0]
        g = Graph(J)
        for r in J[z]:
            a = stl(g, g.lab[z], g.lab[r])
            b = jz_side(J, z, r)
            if a == b:
                agree += 1
            else:
                dis += 1
                print('DISAGREE', l.strip().decode(), z, r, a, b)
    print('n =', n, 'agree', agree, 'disagree', dis)

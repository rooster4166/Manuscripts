"""Sanity checks for the two-even-vertex problem and the second descent step
(endpoint-structure manuscript, Section 5).

Subcommands (n <= 8 uses data/conn{n}.g6):
  census n         tightness of all connected graphs with exactly two even vertices,
                   with the obstruction class (O1), (O2), (O3)/cut vertex, or 'other'
  twins n          every non-realisable pair {u,v} (Ev-{u,v} not realisable) is an E-twin pair
  pair n           the pair step (Theorem 28) on all instances
  residual n       the residual cases of Corollary 29 and Theorem 30: is the step still possible?
  schedule n       every set certified by a Fan schedule is realisable (Theorem 24)
Solver: tools/pathnum.py (CP-SAT exact cover).
"""
import sys, itertools
import networkx as nx
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from pathnum import solve, enumerate_paths, path_number

DATA = __file__.rsplit('/', 2)[0] + '/data/conn{}.g6'


def graphs(n):
    for line in open(DATA.format(n)):
        yield line.strip(), nx.from_graph6_bytes(line.strip().encode())


def realisable(G, S, paths=None):
    odd = [v for v in G if G.degree(v) % 2]
    ex = {v: 1 for v in odd}
    for v in G:
        if G.degree(v) % 2 == 0:
            ex[v] = 2 if v in S else 0
    r = solve(G, budget=len(odd) // 2 + len(S), exact_ends=ex, paths=paths,
              time_limit=120, workers=1)
    return r.value is not None


def tight(H):
    return realisable(H, set())


def etwins(G, ev, u, v):
    return (set(G[u]) & set(ev)) - {u, v} == (set(G[v]) & set(ev)) - {u, v}


def obstruction(H):
    n = H.number_of_nodes()
    u, v = [x for x in H if H.degree(x) % 2 == 0]
    if any(H.degree(w) % 2 and H.degree(w) >= n - 1 for w in H):
        return 'O1'
    if H.degree(u) == 2 and H.degree(v) == 2 and H.has_edge(u, v) and set(H[u]) & set(H[v]):
        return 'O2'
    for a, b in ((u, v), (v, u)):
        if not H.has_edge(a, b) and H.degree(a) == 2 and set(H[a]) == set(H[b]):
            x, y = sorted(H[a])
            if H.has_edge(x, y) and (H.degree(x) == 3 or H.degree(y) == 3):
                return 'O3'
    if nx.node_connectivity(H) <= 1:
        return 'cut'
    return 'other'


def census(n):
    from collections import Counter
    tot, cnt = 0, Counter()
    for s, H in graphs(n):
        ev = [x for x in H if H.degree(x) % 2 == 0]
        if len(ev) != 2:
            continue
        tot += 1
        if any(H.degree(w) % 2 and H.degree(w) >= n - 1 for w in H):
            cnt['O1'] += 1          # proved obstruction, no solve needed
            continue
        if not tight(H):
            c = obstruction(H)
            cnt[c] += 1
            if c == 'other':
                print('OTHER', s, flush=True)
    print(n, 'two-even graphs', tot, 'not tight', sum(cnt.values()), dict(cnt))


def twins(n):
    bad = 0; pairs = 0
    for s, G in graphs(n):
        ev = [x for x in G if G.degree(x) % 2 == 0]
        if len(ev) < 3:
            continue
        P = enumerate_paths(G)
        for u, v in itertools.combinations(ev, 2):
            pairs += 1
            if not etwins(G, ev, u, v) and not realisable(G, set(ev) - {u, v}, P):
                bad += 1; print('VIOLATION', s, u, v, flush=True)
    print(n, 'pairs', pairs, 'violations', bad)


def pair(n):
    tested = bad = 0
    for s, G in graphs(n):
        ev = [x for x in G if G.degree(x) % 2 == 0]
        if len(ev) < 3:
            continue
        P = None; cache = {}
        def R(u, a):
            nonlocal P
            k = frozenset((u, a))
            if k not in cache:
                if P is None:
                    P = enumerate_paths(G)
                cache[k] = realisable(G, set(ev) - {u, a}, P)
            return cache[k]
        for u in ev:
            for a, a2 in itertools.combinations([x for x in ev if x != u], 2):
                for w in set(G[a]) & set(G[a2]):
                    if w == u:
                        continue
                    if G.degree(w) % 2 == 0 and G.degree(w) < 4:
                        continue
                    if G.degree(w) % 2 and G.has_edge(a, a2) and (G.has_edge(a, u) or G.has_edge(a2, u)):
                        continue
                    tested += 1
                    if not (R(u, a) or R(u, a2)):
                        bad += 1; print('VIOLATION', s, u, a, a2, w, flush=True)
                    break
    print(n, 'pair-step instances', tested, 'violations', bad)


def residual(n, sh=0, ns=1):
    nb = nbf = nfd = nfdf = 0
    for li, (s, G) in enumerate(graphs(n)):
        if li % ns != sh:
            continue
        ev = [x for x in G if G.degree(x) % 2 == 0]; e = len(ev)
        if e < 4:
            continue
        od = [x for x in G if G.degree(x) % 2]
        F = G.subgraph(ev)
        P = None; cache = {}
        def R(u, v):
            nonlocal P
            k = frozenset((u, v))
            if k not in cache:
                if P is None:
                    P = enumerate_paths(G)
                cache[k] = realisable(G, set(ev) - {u, v}, P)
            return cache[k]
        for r in ev:
            rest = [x for x in ev if x != r]
            tri = e == 4 and F.subgraph(rest).number_of_edges() == 3 and F.degree(r) == 0
            if tri:
                nb += 1
                if not any(R(u, v) for u, v in itertools.combinations(rest, 2)):
                    nbf += 1; print('B-FAIL', s, r, flush=True)
            for u in rest:
                others = [x for x in ev if x not in (u, r)]
                if tri or (F.number_of_edges() == 0 and
                           all(len(set(G[w]) & set(others)) <= 1 for w in od)):
                    nfd += 1
                    if not any(R(u, v) for v in others):
                        nfdf += 1; print('FD-FAIL', s, u, r, flush=True)
    print(n, 'Thm30-residual', nb, 'fail', nbf, 'Cor29-residual', nfd, 'fail', nfdf)


def schedule(n):
    tot = bad = 0
    for s, G in graphs(n):
        ev = [x for x in G if G.degree(x) % 2 == 0]
        if len(ev) < 2:
            continue
        out = set()
        def rec(X, used):
            out.add(frozenset(X))
            for x in ev:
                if x in used:
                    continue
                for w in ev:
                    if w in used or w == x or not G.has_edge(x, w):
                        continue
                    if any(G.has_edge(w, y) for y in X):
                        continue
                    rec(X | {x}, used | {x, w})
        for x1 in ev:
            rec({x1}, {x1})
        P = enumerate_paths(G)
        for X in out:
            tot += 1
            if not realisable(G, set(ev) - X, P):
                bad += 1; print('VIOLATION', s, sorted(X), flush=True)
    print(n, 'certified sets', tot, 'violations', bad)


if __name__ == '__main__':
    cmd, n = sys.argv[1], int(sys.argv[2])
    args = [int(a) for a in sys.argv[3:]]
    {'census': census, 'twins': twins, 'pair': pair, 'residual': residual,
     'schedule': schedule}[cmd](n, *args)

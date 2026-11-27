#!/usr/bin/env python3
"""Audit A13: an independent exact realisability oracle, and the order-12 EMM counterexamples
(missing-move Thm 7.5) seen through the cut-selection construction of endpoint-min-max Thm 21.

realisable(G, b): is there a partition of E(G) into paths with exactly b(v) ends at every v?
Depth-first search. The smallest vertex s with remaining b(s) > 0 must be an end of some path of
any completion, so the next path is grown from s. Pruning: for every v, the remaining degree d'
and remaining ends b' satisfy b' <= d', b' = d' (mod 2), and a vertex with d' > 0 lies in a
component of the unused edges that still has an end. Memoised on (unused edges, b').

Usage: a13_realis.py selftest [FILE]    compare with the cut checker on data/conn6.g6 or FILE
                                        (EMM holds at n <= 8, so the two must agree)
       a13_realis.py mm12 [trials]      the 12 graphs of missing-move outputs/emm_counterexamples12.g6
"""
import functools
import itertools
import os
import random
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a13_check as C  # noqa: E402


def realisable(G, b):
    n = G.number_of_nodes()
    edges = [C.edge(a, c) for a, c in G.edges()]
    m = len(edges)
    inc = [[] for _ in range(n)]
    for i, (a, c) in enumerate(edges):
        inc[a].append((i, c))
        inc[c].append((i, a))
    if sum(b) % 2:
        return False

    def feasible(U, bb):
        deg = [0] * n
        for i in range(m):
            if U >> i & 1:
                a, c = edges[i]
                deg[a] += 1
                deg[c] += 1
        for v in range(n):
            if bb[v] > deg[v] or (bb[v] - deg[v]) % 2:
                return False
        # each component of U with an edge has an end
        seen = [False] * n
        for v in range(n):
            if deg[v] and not seen[v]:
                stack, has_end = [v], False
                seen[v] = True
                while stack:
                    x = stack.pop()
                    if bb[x]:
                        has_end = True
                    for i, y in inc[x]:
                        if U >> i & 1 and not seen[y]:
                            seen[y] = True
                            stack.append(y)
                if not has_end:
                    return False
        return True

    @functools.lru_cache(maxsize=None)
    def solve(U, bb):
        if U == 0:
            return not any(bb)
        if not feasible(U, bb):
            return False
        s = next(v for v in range(n) if bb[v])
        bl = list(bb)
        bl[s] -= 1
        # grow a path from s
        found = False

        def grow(cur, U2, visited):
            nonlocal found
            if found:
                return
            for i, y in inc[cur]:
                if U2 >> i & 1 and not visited >> y & 1:
                    U3 = U2 & ~(1 << i)
                    if bl[y] > 0:
                        bl[y] -= 1
                        if solve(U3, tuple(bl)):
                            found = True
                        bl[y] += 1
                        if found:
                            return
                    grow(y, U3, visited | (1 << y))
                    if found:
                        return

        grow(s, U, 1 << s)
        return found

    return solve((1 << m) - 1, tuple(b))


def selftest(path='data/conn6.g6'):
    """At n <= 8, EMM holds (manuscript Table 1), so realisable == cut-feasible on every half-set."""
    tot = mism = 0
    for line in open(path):
        G = nx.from_graph6_bytes(line.strip().encode())
        n = G.number_of_nodes()
        deg = [G.degree(v) for v in range(n)]
        Ev = [v for v in range(n) if deg[v] % 2 == 0]
        cd = C.CutData(G)
        for M in itertools.combinations(Ev, len(Ev) // 2):
            b = C.simple_profile(deg, set(M))
            r = realisable(G, b)
            f = cd.profile_ok(b) is None
            tot += 1
            mism += (r != f)
            assert not (r and not f), 'unsound: realisable but cut-infeasible'
    print('selftest', path, ': half-sets', tot, 'realisable != cut-feasible:', mism)


def mm12(trials):
    rng = random.Random(12)
    path = 'manuscripts/missing-move/scripts/outputs/emm_counterexamples12.g6'
    for line in open(path):
        s = line.strip()
        G = nx.from_graph6_bytes(s.encode())
        n = G.number_of_nodes()
        deg = [G.degree(v) for v in range(n)]
        Ev = [v for v in range(n) if deg[v] % 2 == 0]
        cd = C.CutData(G)
        feas, real = {}, {}
        for M in itertools.combinations(Ev, len(Ev) // 2):
            b = C.simple_profile(deg, set(M))
            feas[frozenset(M)] = cd.profile_ok(b) is None
            real[frozenset(M)] = realisable(G, b)
            assert feas[frozenset(M)] or not real[frozenset(M)], 'unsound'
        bad = [sorted(M) for M in feas if feas[M] and not real[M]]
        nreal = sum(real.values())
        # constructed pairings
        stats = {'constructions': 0, 'contain_bad_transversal': 0, 'all_transversals_realisable': 0,
                 'no_realisable_transversal': 0}
        pairings = set()
        for t in range(trials):
            for meth in ('proof', 'greedy'):
                P, routes, J, st = C.construct(nx.convert_node_labels_to_integers(G), rng, meth)
                stats['constructions'] += 1
                pairings.add(frozenset(frozenset(p) for p in P))
                trans = [frozenset(p[c] for p, c in zip(P, ch))
                         for ch in itertools.product((0, 1), repeat=len(P))]
                assert all(feas[M] for M in trans), 'constructed pairing not good'
                if any(not real[M] for M in trans):
                    stats['contain_bad_transversal'] += 1
                if all(real[M] for M in trans):
                    stats['all_transversals_realisable'] += 1
                if not any(real[M] for M in trans):
                    stats['no_realisable_transversal'] += 1
        d2 = sum(1 for v in Ev if deg[v] == 2)
        print(s, 'e =', len(Ev), 'even deg-2:', d2, 'half-sets', len(feas), 'cut-feasible',
              sum(feas.values()), 'realisable', nreal, 'cut-feasible & non-realisable:', bad,
              '| distinct pairings', len(pairings), stats, flush=True)


if __name__ == '__main__':
    if sys.argv[1] == 'selftest':
        selftest(sys.argv[2] if len(sys.argv) > 2 else 'data/conn6.g6')
    elif sys.argv[1] == 'mm12':
        mm12(int(sys.argv[2]) if len(sys.argv) > 2 else 20)

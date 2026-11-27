#!/usr/bin/env python3
"""Audit A13: for each order-12 EMM counterexample (missing-move outputs/emm_counterexamples12.g6),
enumerate ALL pairings of Ev, find the good ones (every transversal cut-feasible, brute force), and
test whether the cut-feasible non-realisable half-set M is a transversal of some good pairing,
and whether every transversal of every good pairing is realisable."""
import itertools
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a13_check as C  # noqa: E402
from a13_realis import realisable  # noqa: E402

for line in open('manuscripts/missing-move/scripts/outputs/emm_counterexamples12.g6'):
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
    bad = [M for M in feas if feas[M] and not real[M]]
    good = 0
    bad_in_good = 0
    nonreal_in_good = 0
    union = set()
    for P in C.all_pairings(Ev):
        trans = [frozenset(p[c] for p, c in zip(P, ch)) for ch in itertools.product((0, 1), repeat=len(P))]
        if all(feas[M] for M in trans):
            good += 1
            union |= set(trans)
            if any(M in bad for M in trans):
                bad_in_good += 1
            if any(not real[M] for M in trans):
                nonreal_in_good += 1
    for M in bad:
        comp = frozenset(Ev) - M
        print(s, 'bad M', sorted(M), 'complement cut-feasible:', feas[comp],
              '| pairings', sum(1 for _ in C.all_pairings(Ev)), 'good', good,
              'good with M as transversal', bad_in_good,
              'good with a non-realisable transversal', nonreal_in_good,
              '| union of transversals of good pairings:', len(union), 'of', sum(feas.values()), 'cut-feasible')

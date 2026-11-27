"""Audit A22c: sensitivity check of construct.py, and necessity of each of the six separations for
the proof: drop one pair from the base requirement and execute the proof (order 9, simple pairings,
walk3 chains).  A failed claim shows that the proof uses that pair."""
import sys, collections
import chain, construct
from count_J import g6_decode, pairings
from dlib import solve

fn = sys.argv[1]
lines = [l.split()[0] for l in open(fn) if l.strip()]
orig = chain.six_pairs
for drop in range(6):
    def sp(X, Y, l1, drop=drop):
        p = orig(X, Y, l1); return p[:drop] + p[drop + 1:]
    construct.six_pairs = sp
    stat = collections.Counter(); fails = collections.Counter()
    for s in lines[::3]:
        n, B = g6_decode(s)
        deg = [sum(r) for r in B]
        ev = [v for v in range(n) if deg[v] % 2 == 0]
        E0 = {frozenset((u, v)) for v in range(n) for u in range(v) if B[u][v]}
        for F in pairings(ev):
            if any(B[a][b] for a, b in F): continue
            E = E0 | {frozenset(p) for p in F}
            for X, Y in chain.configs(F):
                for P2, P1 in chain.chains(n, E, X, Y):
                    for sd in range(3):
                        try:
                            r = construct.run(n, E, X, Y, P2, P1, seed=sd)
                            if r is None: break
                            stat['ok'] += 1
                        except construct.ClaimFailed as e:
                            stat['fail'] += 1; fails[str(e).split(' = ')[0]] += 1
                    break
    print('dropped', orig((1, 2, 3), (4, 5, 6), 'l1')[drop], dict(stat), dict(fails.most_common(3)))

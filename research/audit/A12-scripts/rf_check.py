"""Receipt or flower with a count (missing-move Lemma 5.9) and the orbit rule, in the independent
solver game.py (audit A12). Held sets: a full star (one per vertex, up to automorphism) plus k
further edges. Prints the roots won with and without rf, with and without the orbit rule.
Usage: nice python3 rf_check.py GRAPH6 kmax"""
import sys, time
from itertools import combinations
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
import game

g6, kmax = sys.argv[1], int(sys.argv[2])
G = nx.from_graph6_bytes(g6.encode())
n = G.number_of_nodes()
autos = [tuple(a[v] for v in range(n)) for a in GraphMatcher(G, G).isomorphisms_iter()]
for rf in (False, True):
    for orbit in (False, True):
        gm = game.Game(n, list(G.edges()), newpath=True, rf=rf, autos=autos if orbit else None)
        eperm = [[gm.eid[tuple(sorted((p[a], p[c])))] for (a, c) in gm.E] for p in autos]
        t = time.time()
        for k in range(0, kmax + 1):
            won = 0; seen = set()
            for h in range(n):
                star = list(gm.inc[h]); rest = [i for i in range(gm.m) if i not in star]
                for X in combinations(rest, k):
                    key = min(tuple(sorted(p[i] for i in star + list(X))) for p in eperm)
                    if key in seen:
                        continue
                    seen.add(key)
                    Fs, sd = gm.seeds(key)
                    for kind, b0 in sd:
                        won |= gm.value(Fs, b0)
            clo = 0
            for p in autos:
                for v in range(n):
                    if (won >> v) & 1:
                        clo |= 1 << p[v]
            print(f"{g6} rf={rf} orbit={orbit} star+{k}: roots won {[r for r in range(n) if (clo >> r) & 1]} "
                  f"({round(time.time() - t)} s)", flush=True)

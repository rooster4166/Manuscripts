"""K8 minus a perfect matching (Gr~v~w = CP(4)) in the Fan game with path insertion (game.py).

(a) The |F| = 9 held set of outputs/certificate_K8M.txt wins at the root 0.
(b) Every held set with |F| <= KMAX (default 8) loses at every root. Held sets are taken up to the
    automorphism group of the graph (order 384): if F wins at r then phi(F) wins at phi(r), and the
    solver returns the set of winning roots of each (F, seed).
Usage: nice python3 k8pm.py [KMAX]"""
import sys, time
from itertools import combinations, permutations
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
import game

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 8
n, E = game.from_g6('Gr~v~w')
G = nx.Graph(); G.add_edges_from(E)
comp = sorted(set((a, b) for a in range(8) for b in range(a + 1, 8)) - set(map(tuple, map(sorted, E))))
print("complement (the matching):", comp)
assert all(d == 6 for _, d in G.degree())
gm = game.Game(n, E, newpath=True)
autos = [tuple(a[v] for v in range(n)) for a in GraphMatcher(G, G).isomorphisms_iter()]
print("automorphisms:", len(autos))
eperm = [[gm.eid[tuple(sorted((p[a], p[c])))] for (a, c) in gm.E] for p in autos]

# (a) the certificate's held set
Fc = [(0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (2, 4)]
F = [gm.eid[e] for e in Fc]
Fs, sd = gm.seeds(F)
for kind, b0 in sd:
    v = gm.value(Fs, b0)
    print("(a) F =", Fc, "seed", kind, b0, "winning roots:", [r for r in range(n) if (v >> r) & 1], flush=True)

# (b) all held sets up to |F| = KMAX
def ok_seed(F):
    dF = [0] * n
    for i in F:
        a, c = gm.E[i]; dF[a] += 1; dF[c] += 1
    ev = sum(1 for d in dF if d in (0, 2, 4))          # positive even degree in K
    if ev <= 1:
        return True
    return ev == 2 and all(d < 6 for d in dF)

for k in range(0, KMAX + 1):
    t = time.time(); seen = set(); nreps = 0; won = 0
    for F in combinations(range(gm.m), k):
        if not ok_seed(F):
            continue
        key = min(tuple(sorted(p[i] for i in F)) for p in eperm)
        if key in seen:
            continue
        seen.add(key); nreps += 1
        Fs, sd = gm.seeds(key)
        for kind, b0 in sd:
            won |= gm.value(Fs, b0)
    print("(b) |F| =", k, "orbit representatives with a seed:", nreps, "winning roots:",
          [r for r in range(n) if (won >> r) & 1], round(time.time() - t), "s, states", len(gm.memo), flush=True)
    if len(gm.memo) > 25_000_000:
        gm.memo.clear()

"""Hub-shaped held sets (a full star plus k further edges) at order 10, with the independent solver
game.py (path insertion; no receipt-or-flower, no flower, no orbit rule). Audit A12.

For each k in kmin..kmax prints the set of roots won by some held set star(h) + X, |X| = k
(exact masks, so all roots at once), and the first held set found for each root.
Usage: nice python3 hubrun.py GRAPH6 kmin kmax [nonp]"""
import sys, time
from itertools import combinations
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
import game

g6, kmin, kmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
G = nx.from_graph6_bytes(g6.encode())
n = G.number_of_nodes()
gm = game.Game(n, list(G.edges()), newpath="nonp" not in sys.argv[4:])
autos = [tuple(a[v] for v in range(n)) for a in GraphMatcher(G, G).isomorphisms_iter()]
eperm = [[gm.eid[tuple(sorted((p[a], p[c])))] for (a, c) in gm.E] for p in autos]
d = dict(G.degree())
print(g6, "n", n, "|E|", gm.m, "Ev", [v for v in G if d[v] % 2 == 0], "|Aut|", len(autos), flush=True)
first = {}
for k in range(kmin, kmax + 1):
    t = time.time(); won = 0; seen = set(); cnt = 0
    for h in range(n):
        star = [i for i in gm.inc[h]]
        rest = [i for i in range(gm.m) if i not in star]
        for X in combinations(rest, k):
            F = tuple(sorted(star + list(X)))
            key = min(tuple(sorted(p[i] for i in F)) for p in eperm)
            if key in seen:
                continue
            seen.add(key)
            Fs, sd = gm.seeds(key)
            for kind, b0 in sd:
                cnt += 1
                v = gm.value(Fs, b0)
                for r in range(n):
                    if (v >> r) & 1 and r not in first:
                        first[r] = (k, [gm.E[i] for i in key], kind)
                won |= v
    clo = 0
    for p in autos:
        for v in range(n):
            if (won >> v) & 1:
                clo |= 1 << p[v]
    print(f"star + {k}: {len(seen)} held sets up to Aut, {cnt} seeded; roots won: "
          f"{[r for r in range(n) if (clo >> r) & 1]}  ({round(time.time() - t)} s, {len(gm.memo)} states)", flush=True)
    if len(gm.memo) > 15_000_000:
        gm.memo.clear()
for r in sorted(first):
    print("root", r, "first win:", first[r])

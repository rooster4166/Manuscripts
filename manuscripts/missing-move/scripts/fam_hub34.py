import sys, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx, fan_game as fg
from networkx.algorithms.isomorphism import GraphMatcher
fg.CACHE_CAP = 800_000
name, k = sys.argv[1], int(sys.argv[2])
G = nx.read_graph6(name + ".g6")
autos = list(GraphMatcher(G, G).isomorphisms_iter())
seen = set(); reps = []
for v in sorted(G):
    if v in seen: continue
    orb = {a[v] for a in autos}; seen |= orb; reps.append((v, sorted(orb)))
for r, orb in reps:
    t = time.time()
    res = fg.solve_graph(G, k, roots=[r], newpath=True, hubs=True, kmin=k)
    print(name, "hubs k", k, "root", r, "orbit", orb, ":", res[r], "time", round(time.time() - t), flush=True)

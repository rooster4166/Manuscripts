"""Run the game with path insertion at one root and exactly one held-set size (kmin = kmax = k).
Usage: python3 single_root.py GRAPH6 ROOT K   (e.g. Gr~v~w 0 8: K8 minus a matching loses at |F| = 8)."""
import sys, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx, fan_game as fg
fg.CACHE_CAP = 800_000
G = nx.from_graph6_bytes(sys.argv[1].encode()); r = int(sys.argv[2]); k = int(sys.argv[3])
t = time.time()
res = fg.solve_graph(G, k, roots=[r], newpath=True, kmin=k)
print(sys.argv[1], "k", k, "root", r, ":", res[r], "time", round(time.time() - t), flush=True)

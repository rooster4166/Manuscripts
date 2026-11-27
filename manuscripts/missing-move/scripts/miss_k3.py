"""Inv~|~zbw at roots 2 and 3 with a star plus exactly k held edges (np, rf, orbit)."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx, fan_game as fg
fg.CACHE_CAP = 800_000
G = nx.from_graph6_bytes(b'Inv~|~zbw'); k = int(sys.argv[1])
for r in (2, 3):
    t = time.time()
    res = fg.solve_graph(G, k, roots=[r], newpath=True, hubs=True, rf=True, orbit=True, kmin=k)
    print("root", r, "star +", k, ":", res[r], "time", round(time.time() - t), flush=True)

"""allodd8.py -- audit A21: Theorem 1.3 (prescribed end edge, all degrees odd) on all connected
all-odd graphs of order 8, with the independent solver ts.  Counts ordered edges (x, y) with
d(x) >= 3 (the manuscript's convention) and with any d(x)."""
import os, subprocess, collections
import networkx as nx
from exhaust import Solver

HERE = os.path.dirname(os.path.abspath(__file__))
S = Solver(os.path.join(HERE, "ts"))
C = collections.Counter()
for line in subprocess.run(["nauty-geng", "-cq", "8"], capture_output=True, text=True).stdout.split():
    G = nx.from_graph6_bytes(line.encode())
    if any(G.degree(v) % 2 == 0 for v in G):
        continue
    C["graphs"] += 1
    for x in G:
        for y in G[x]:
            C["arcs_all"] += 1
            if G.degree(x) < 3:
                continue
            C["arcs_dx>=3"] += 1
            if S.ask(G, f"T {x} {y}") == 0:
                C["fail"] += 1
                print("FAIL", line, x, y)
print(dict(C))

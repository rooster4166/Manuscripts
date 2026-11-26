"""Independent check of the rooted test: for each root r, a partition into <= n/2 paths with an
end at r, found by CP-SAT (tools/pathnum2.py). Also the simple-profile form (b = 1 on odd
vertices, b in {0, 2} on even ones) with b(r) = 2 for even r."""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from pathnum2 import decompose
for path in sys.argv[1:]:
    for line in open(path):
        line = line.strip()
        if not line: continue
        G = nx.from_graph6_bytes(line.encode()); n = G.number_of_nodes(); d = dict(G.degree())
        out = []
        for r in G:
            st, paths = decompose(G, n // 2, min_ends={r: 1}, time_limit=60, workers=2)
            out.append((r, st if paths is None else len(paths)))
        print(line, out, flush=True)

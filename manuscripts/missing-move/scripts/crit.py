"""p(G) < n/2 ? via CP-SAT (pathnum2): is there a partition into n/2 - 1 paths?"""
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from pathnum2 import decompose
for path in sys.argv[1:]:
    for line in open(path):
        g = line.strip()
        if not g: continue
        G = nx.from_graph6_bytes(g.encode()); n = G.number_of_nodes()
        st, paths = decompose(G, n // 2 - 1, time_limit=120, workers=2)
        print(g, "critical" if paths is None and st in ("INFEASIBLE",) else ("NONCRITICAL" if paths else st), flush=True)

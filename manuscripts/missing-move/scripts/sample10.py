"""A small sample of critical connected graphs of order 10 with a vertex of degree 6."""
import random, sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from pathnum2 import decompose
random.seed(int(sys.argv[1])); want = int(sys.argv[2]); found = 0; tries = 0
while found < want and tries < 400:
    tries += 1
    G = nx.gnp_random_graph(10, random.uniform(0.45, 0.75), seed=random.randrange(10**9))
    if not nx.is_connected(G): continue
    d = dict(G.degree())
    if 6 not in d.values(): continue
    st, paths = decompose(G, 4, time_limit=60, workers=2)
    if paths is None and st == "INFEASIBLE":
        found += 1
        print(nx.to_graph6_bytes(G, header=False).decode().strip(), flush=True)

"""Classify critical graphs (even order n, p = n/2, at least one even vertex) by
what forces p >= n/2: universal vertex (Delta = n-1), edge count
(m > (n/2-1)(n-1)), all vertices odd (excluded here), or none of these ('rigid')."""
import sys
from collections import Counter
import networkx as nx
from pathnum import solve

cnt = Counter(); rigid = []
for line in open(sys.argv[1]):
    G = nx.from_graph6_bytes(line.strip().encode())
    n = G.number_of_nodes(); m = G.number_of_edges()
    if not any(G.degree(v) % 2 == 0 for v in G):
        continue
    D = max(d for _, d in G.degree())
    if D == n - 1:
        cnt["universal vertex"] += 1; continue
    if m > (n // 2 - 1) * (n - 1):
        cnt["edge count"] += 1; continue
    r = solve(G, budget=n // 2 - 1, time_limit=120, workers=1)
    if r.status in ("OPTIMAL", "FEASIBLE"):
        cnt["non-critical"] += 1
    else:
        cnt["RIGID critical"] += 1; rigid.append(line.strip())
        print("RIGID", line.strip(), "m", m, "Delta", D, "degs", sorted(d for _, d in G.degree()), flush=True)
print(dict(cnt), flush=True)

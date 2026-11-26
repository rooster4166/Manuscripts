"""TEL1': H connected with at most one even vertex.  For every odd vertex v and
every edge vy there is a decomposition into floor(|H|/2) paths (so every odd
vertex has exactly one end and the even vertex none) whose end at v uses vy.
Also checks the consequence: for G of even order, E - {u, v} realisable for all
pairs of even vertices u != v.
"""
import sys
import networkx as nx
from terminal_edge import feasible

tot = fails = 0
for line in open(sys.argv[1]):
    H = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(line.strip().encode()))
    ev = [v for v in H if H.degree(v) % 2 == 0]
    if len(ev) > 1:
        continue
    tot += 1
    for v in H:
        if H.degree(v) % 2 == 0:
            continue
        for y in H[v]:
            if not feasible(H, [(v, y)]):
                fails += 1
                print("TEL1'-FAIL", line.strip(), "even", ev, "v", v, "y", y, flush=True)
print(f"graphs with <=1 even vertex: {tot}; TEL1' failures: {fails}", flush=True)

import sys, collections
import networkx as nx
C = collections.Counter()
for line in open(sys.argv[1]):
    if not line.startswith("FAIL"): continue
    p = line.split(); G = nx.from_graph6_bytes(p[1].encode())
    x = int(p[2][2:]); y = int(p[3][2:]); z = int(p[4][2:])
    dxz = nx.shortest_path_length(G, x, z); dyz = nx.shortest_path_length(G, y, z)
    C[(G.degree(x), G.degree(y), G.degree(z), dxz, dyz, len(set(G[x]) & set(G[z])), int(G.has_edge(x,z)))] += 1
print("(d(x), d(y), d(z), dist(x,z), dist(y,z), |N(x)&N(z)|, x~z): count")
for k, v in sorted(C.items()): print(k, v)

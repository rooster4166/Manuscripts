"""feat9.py -- audit A21: purely combinatorial checks of the authors' exhaustive FAIL lists.

usage: python3 feat9.py out/exh9.txt

For each FAIL line: z is the unique positive even vertex, xy an edge, y != z, d(x) >= 3; then the
features quoted in the manuscript: reachability (Theorem 6.1 definition), y in N(z), dist(x, z),
d(x), d(z).  No solver is used."""
import sys, collections
import networkx as nx
from exhaust import reachable

C = collections.Counter()
for line in open(sys.argv[1]):
    if not line.startswith("FAIL"):
        continue
    p = line.split()
    kv = dict(t.split("=") for t in p[2:5])
    G = nx.from_graph6_bytes(p[1].encode())
    x, y, z = int(kv["x"]), int(kv["y"]), int(kv["z"])
    ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    assert ev == [z] and G.has_edge(x, y) and y != z and G.degree(x) >= 3 and p[5] == "away"
    C["fails"] += 1
    C["reachable" if reachable(G, z, x, y) else "unreachable"] += 1
    C[f"y_in_Nz={G.has_edge(y, z)}"] += 1
    C[f"dist_xz={nx.shortest_path_length(G, x, z)}"] += 1
    C[f"dx={G.degree(x)}"] += 1
    C[f"dz={G.degree(z)}"] += 1
C["distinct_graphs"] = len({l.split()[1] for l in open(sys.argv[1]) if l.startswith("FAIL")})
for k in sorted(C):
    print(f"{k} = {C[k]}")

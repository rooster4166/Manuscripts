"""For each PEE failure (x, y) away from z: is every z-y path blocked by N[x] in its interior?
Prediction (Fan protection + EE): a failure forces this.  Also count, over ALL away edges, how often
the blocking holds, and how often PEE fails given blocking."""
import sys, collections, subprocess, os
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))

def blocked(G, z, x, y):
    # path z = e0, e1..e_{k-1} not in N[x], e_k = y, k >= 1
    if G.has_edge(z, y): return False
    Nx = set(G[x]) | {x}
    H = G.subgraph([v for v in G if v not in Nx] + [z]).copy()   # interior vertices allowed
    # need a vertex e_{k-1} in H reachable from z with e_{k-1} ~ y (e_{k-1} != z handled above)
    comp = nx.node_connected_component(H, z)
    return not any(G.has_edge(v, y) for v in comp if v != z)

if __name__ == "__main__":
    C = collections.Counter()
    if __name__ != "__main__": pass
    fails = set()
    for line in open(sys.argv[1]):
        if line.startswith("FAIL"):
            p = line.split(); fails.add((p[1], int(p[2][2:]), int(p[3][2:])))
    for (g6, x, y) in fails:
        G = nx.from_graph6_bytes(g6.encode())
        z = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0][0]
        C["fail_blocked" if blocked(G, z, x, y) else "fail_NOT_blocked"] += 1
    print(dict(C))

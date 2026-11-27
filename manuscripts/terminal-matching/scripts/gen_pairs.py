"""Emit 'g6(G-F) a1 b1 a2 b2' for every 2-matching F of every all-odd graph G read (g6) from stdin.
Optional argv[1] = 'conn': only instances with G - F connected."""
import sys, itertools
import networkx as nx
conn = len(sys.argv) > 1 and sys.argv[1] == 'conn'
for line in sys.stdin:
    s = line.strip()
    if not s: continue
    G = nx.from_graph6_bytes(s.encode())
    if any(d % 2 == 0 for _, d in G.degree()): continue
    E = sorted(G.edges())
    for e, f in itertools.combinations(E, 2):
        if set(e) & set(f): continue
        H = G.copy(); H.remove_edges_from([e, f])
        if conn and not nx.is_connected(H): continue
        print(nx.to_graph6_bytes(H, header=False).decode().strip(), e[0], e[1], f[0], f[1])

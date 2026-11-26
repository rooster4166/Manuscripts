import networkx as nx, sys
def A(q, m):
    """K_q of even vertices, a full vertex x with a leaf, m false twins adjacent exactly to Q."""
    G = nx.Graph(); Q = list(range(q))
    G.add_edges_from((a, b) for i, a in enumerate(Q) for b in Q[i+1:])
    x, l = q, q + 1
    G.add_edges_from((x, a) for a in Q); G.add_edge(x, l)
    for j in range(m):
        t = q + 2 + j
        G.add_edges_from((t, a) for a in Q)
    return G
def B():
    """d6-frontier style: U = K6 even core, two adjacent full vertices x1, x2, and x3, x4 each
    adjacent to half of U."""
    G = nx.Graph(); U = list(range(6))
    G.add_edges_from((a, b) for i, a in enumerate(U) for b in U[i+1:])
    x1, x2, x3, x4 = 6, 7, 8, 9
    G.add_edges_from((x, u) for x in (x1, x2) for u in U); G.add_edge(x1, x2)
    G.add_edges_from((x3, u) for u in U[:3]); G.add_edges_from((x4, u) for u in U[3:])
    return G
def B2():
    """K6 core, one full vertex x1 with a leaf, and x3, x4 each adjacent to half of U plus
    a common neighbour... (n = 10): x1 full + leaf l; u needs one more odd contact."""
    G = nx.Graph(); U = list(range(6))
    G.add_edges_from((a, b) for i, a in enumerate(U) for b in U[i+1:])
    x1, l, x3, x4 = 6, 7, 8, 9
    G.add_edges_from((x1, u) for u in U); G.add_edge(x1, l)
    # each u has 5 + 1 = 6 so far: needs an even number more -> 0 or 2; x3, x4 adjacent to all
    # of U makes u degree 8 and x3, x4 degree 6 (even): join x3 x4 to make them odd.
    G.add_edges_from((x, u) for x in (x3, x4) for u in U); G.add_edge(x3, x4)
    return G
fams = {"A44": A(4, 4), "A62": A(6, 2), "B": B(), "B2": B2()}
for name, G in fams.items():
    d = dict(G.degree())
    assert nx.is_connected(G) and G.number_of_nodes() % 2 == 0
    print(name, nx.to_graph6_bytes(G, header=False).strip().decode(), "n", G.number_of_nodes(),
          "Ev", [v for v in G if d[v] % 2 == 0], file=sys.stderr)
    open(name + ".g6", "w").write(nx.to_graph6_bytes(G, header=False).decode())

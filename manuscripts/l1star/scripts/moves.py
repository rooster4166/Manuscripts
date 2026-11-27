"""Which reductions apply to an L1*-instance (G, c, A)?  (l1star session, exploratory)

Instance: G with exactly one vertex g of positive even degree, c odd, A disjoint from N[c] u N(g).
Moves (see manuscripts/l1star):
  M1: some u in N(g) has N(u) & A <= {g}           (delete gu; Fan towards u)
  M2: g not in A and g, c connected in G - A        (delete a chordless g-c route; append)
  M9: a route g e1 .. ek (k >= 2) with every ei outside A u N[c] and N(ek) & A empty
                                                    (delete the route; Fan transfers back along it)
usage: nauty-geng -cq n | python3 moves.py K   (|A| <= K; K = 0 means A = Amax only)
"""
import sys, itertools, collections
import networkx as nx

K = int(sys.argv[1])
C = collections.Counter()
for line in sys.stdin:
    G = nx.from_graph6_bytes(line.strip().encode())
    ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    if len(ev) != 1:
        continue
    g = ev[0]
    Ng = set(G[g])
    for c in G:
        if G.degree(c) % 2 == 0 or c in Ng:
            continue
        Nc = set(G[c]) | {c}
        cand = [v for v in G if v not in Nc and v not in Ng]
        sets = [tuple(cand)] if K == 0 else [S for k in range(1, K + 1) for S in itertools.combinations(cand, k)]
        for S in sets:
            A = set(S)
            m1 = any(not ((set(G[u]) & A) - {g}) for u in Ng)
            m2 = g not in A and nx.has_path(G.subgraph(set(G) - A), g, c)
            # M9: vertices allowed on the route after g
            allowed = set(G) - A - Nc - {g}
            H = G.subgraph(allowed | {g})
            reach = nx.node_connected_component(H, g) - {g} if len(H) else set()
            m9 = any(not (set(G[z]) & A) for z in reach if z not in Ng or True)
            key = ("M1" if m1 else "") + ("M2" if m2 else "") + ("M9" if m9 else "")
            C[key or "NONE"] += 1
            if not key and C["NONE"] <= 5:
                print("IRRED", line.strip(), "g", g, "c", c, "A", sorted(A))
print(dict(C))

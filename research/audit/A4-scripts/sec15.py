import sys, itertools
from common import *
sys.path.insert(0, '/home/user/Manuscripts/tools')
from graphgen import connected_graphs
from pathnum import path_number

def relabel(G, tag):
    return nx.relabel_nodes(G, {v: (tag, v) for v in G.nodes()})

def eta(X, x):
    p = path_number(X)
    r = solve(X, budget=p, min_ends={x: 1})
    return 0 if r.status in ("OPTIMAL", "FEASIBLE") else 1

def p_leaves(D, x, i):
    G = D.copy()
    for j in range(i):
        G.add_edge(x, ("leaf", j))
    return path_number(G)

bad = []
cnt = {"t43": 0, "t46hub": 0, "bridge": 0, "diamond": 0, "p1eq": 0}
for j in range(2, 6):
    for X in connected_graphs(j):
        X = nx.convert_node_labels_to_integers(X)
        pX = path_number(X)
        for x in X.nodes():
            et = eta(X, x)
            # Theorem 43 with K_{2h+1}, h = 1, 2
            for h in (1, 2):
                if j == 5 and h == 2 and X.number_of_edges() > 7: continue
                Y = nx.union(relabel(X, 'X'), relabel(nx.complete_graph(2 * h + 1), 'Z'))
                Y.add_edge(('X', x), ('Z', 0))
                pY = path_number(Y)
                cnt["t43"] += 1
                if pY != pX + h + et: bad.append(("t43", nx.to_graph6_bytes(X), x, h, pY, pX, et))
            # hub with 3 copies (Theorem 46 / Prop 45)
            if j <= 4:
                Y = nx.union_all([relabel(X, c) for c in range(3)])
                for c in range(3): Y.add_edge('hub', (c, x))
                pY = path_number(Y)
                cnt["t46hub"] += 1
                if pY != 3 * (pX + et) - 1: bad.append(("hub", nx.to_graph6_bytes(X), x, pY, pX, et))
print("Thm43/Prop45 checks", cnt, "bad", bad[:5], flush=True)

# Theorem 50 identities on 2-connected cores
for n in (3, 4, 5, 6):
    for D in connected_graphs(n):
        D = nx.convert_node_labels_to_integers(D)
        if nx.node_connectivity(D) < 2: continue
        for x in D.nodes():
            dx = D.degree(x)
            if n % 2 == 0 and n <= 6 and dx % 2 == 0:
                p1 = p_leaves(D, x, 1)
                Y = nx.union(relabel(D, 'A'), relabel(D, 'B')); Y.add_edge(('A', x), ('B', x))
                pY = path_number(Y); cnt["bridge"] += 1
                if pY != 2 * p1 - 1: bad.append(("bridge", nx.to_graph6_bytes(D), x, pY, p1))
            if n % 2 == 1 and dx % 2 == 1:
                p2 = p_leaves(D, x, 2)
                Y = nx.union(relabel(D, 'A'), relabel(D, 'B'))
                Y = nx.relabel_nodes(Y, {('A', x): 'xa', ('B', x): 'xb'})
                Y.add_edges_from([('xa', 'a'), ('xa', 'b'), ('xb', 'a'), ('xb', 'b'), ('a', 'b')])
                pY = path_number(Y); cnt["diamond"] += 1
                if pY != 2 * p2 - 1: bad.append(("diamond", nx.to_graph6_bytes(D), x, pY, p2))
            # p_i(D,x) = p(D + i leaves) check against direct min-with-ends
            for i in (1, 2):
                if D.number_of_edges() > 12: continue
                direct = solve(D, min_ends={x: i})
                if direct.value != p_leaves(D, x, i): bad.append(("p_i", nx.to_graph6_bytes(D), x, i, direct.value))
                cnt["p1eq"] += 1
print("Thm50 checks", cnt, "bad", bad[:5], flush=True)

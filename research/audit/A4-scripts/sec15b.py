import sys, itertools
from common import *
import sys; sys.path.insert(0, "/home/user/Manuscripts/tools")
from graphgen import connected_graphs
def relabel(G, tag): return nx.relabel_nodes(G, {v: (tag, v) for v in G.nodes()})
def pn(G, tl=900):
    r = solve(G, time_limit=tl)
    if r.status == "OPTIMAL": return r.value
    lb = solve(G, budget=r.value - 1, time_limit=tl)
    return r.value if lb.status == "INFEASIBLE" else None
def p_leaves(D, x, i):
    G = D.copy()
    for j in range(i): G.add_edge(x, ("leaf", j))
    return pn(G)
bad = []; cnt = {"bridge": 0, "diamond": 0, "p_i": 0, "unknown": 0}
for n in (3, 4, 5, 6):
    for D in connected_graphs(n):
        D = nx.convert_node_labels_to_integers(D)
        if nx.node_connectivity(D) < 2: continue
        orbits = {}
        for x in D.nodes():
            orbits.setdefault(nx.weisfeiler_lehman_graph_hash(D, iterations=3) + str(D.degree(x)) + str(sorted(D.degree(y) for y in D[x])), x)
        for x in orbits.values():
            dx = D.degree(x)
            for i in (1, 2):
                direct = solve(D, min_ends={x: i}).value
                if direct != p_leaves(D, x, i): bad.append(("p_i", nx.to_graph6_bytes(D), x, i))
                cnt["p_i"] += 1
            if n % 2 == 0 and dx % 2 == 0:
                p1 = p_leaves(D, x, 1)
                Y = nx.union(relabel(D, 'A'), relabel(D, 'B')); Y.add_edge(('A', x), ('B', x))
                pY = pn(Y)
                if pY is None: cnt["unknown"] += 1; continue
                cnt["bridge"] += 1
                if pY != 2 * p1 - 1: bad.append(("bridge", nx.to_graph6_bytes(D), x, pY, p1))
            if n % 2 == 1 and dx % 2 == 1:
                p2 = p_leaves(D, x, 2)
                Y = nx.union(relabel(D, 'A'), relabel(D, 'B'))
                Y = nx.relabel_nodes(Y, {('A', x): 'xa', ('B', x): 'xb'})
                Y.add_edges_from([('xa', 'a'), ('xa', 'b'), ('xb', 'a'), ('xb', 'b'), ('a', 'b')])
                pY = pn(Y)
                if pY is None: cnt["unknown"] += 1; continue
                cnt["diamond"] += 1
                if pY != 2 * p2 - 1: bad.append(("diamond", nx.to_graph6_bytes(D), x, pY, p2))
    print("n", n, cnt, "bad", bad[:5], flush=True)

import networkx as nx, sys
sys.path.insert(0, '/home/user/Manuscripts/tools')
from pathnum import solve
def relabel(G, t): return nx.relabel_nodes(G, {v: (t, v) for v in G})
def pn(G):
    r = solve(G, time_limit=300); return r.value if r.status == "OPTIMAL" else None
cases = {"K23": nx.complete_bipartite_graph(2, 3), "house": nx.Graph([(0,1),(1,2),(2,3),(3,4),(4,0),(1,4)]),
         "C5": None}
del cases["C5"]
for name, D in cases.items():
    D = nx.convert_node_labels_to_integers(D)
    for x in [v for v in D if D.degree(v) % 2 == 1][:1]:
        D2 = D.copy(); D2.add_edges_from([(x, 'l1'), (x, 'l2')]); p2 = pn(D2)
        Y = nx.union(relabel(D, 'A'), relabel(D, 'B')); Y = nx.relabel_nodes(Y, {('A', x): 'xa', ('B', x): 'xb'})
        Y.add_edges_from([('xa','a'),('xa','b'),('xb','a'),('xb','b'),('a','b')])
        pY = pn(Y)
        print(name, "x", x, "p2", p2, "p(diamond double)", pY, "identity 2p2-1 =", 2*p2-1, "OK" if pY == 2*p2-1 else "MISMATCH", flush=True)

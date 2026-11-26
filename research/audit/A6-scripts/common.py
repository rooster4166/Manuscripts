import sys, itertools
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from pathnum import solve, enumerate_paths, verify_partition, path_number

SHAPES = {}
def dshape(G, U, r):
    """Return (shape name, r-position-ok) for D = K6 - G[U]."""
    D = nx.Graph(); D.add_nodes_from(U)
    for a, b in itertools.combinations(U, 2):
        if not G.has_edge(a, b):
            D.add_edge(a, b)
    E = D.number_of_edges()
    nonis = [v for v in U if D.degree(v) > 0]
    H = D.subgraph(nonis)
    name = None
    if E == 0: name = 'empty'
    elif E == 1: name = 'K2'
    elif E == 2 and nx.is_connected(H) and len(nonis) == 3: name = 'P3'
    elif E == 3 and len(nonis) == 3: name = 'K3'
    elif E == 4 and len(nonis) == 4 and all(D.degree(v) == 2 for v in nonis): name = 'C4'
    else: name = 'other'
    # candidate status of r per RS table
    coreneigh = any(G.has_edge(r, u) for u in U if u != r)
    if not coreneigh:
        T = [u for u in U if u != r]
        miss = [(a, b) for a, b in itertools.combinations(T, 2) if not G.has_edge(a, b)]
        Dm = nx.Graph(miss)
        iso_ok = (len(miss) == 0 or len(miss) == 1 or (len(miss) == 2 and len(set(sum(miss, ()))) == 3))
        return name + '+isolated', iso_ok
    if name in ('empty', 'K2'): cand = True
    elif name == 'P3': cand = D.degree(r) == 2
    elif name == 'K3': cand = D.degree(r) == 2
    elif name == 'C4': cand = D.degree(r) == 2
    else: cand = False
    return name, cand

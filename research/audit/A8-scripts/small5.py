import networkx as nx, itertools
from networkx.generators.atlas import graph_atlas_g
exec(open('gen7.py').read().split("gs=[G for G")[0])
def closure_calG_bruteforce(G,extra=0):
    # is G a subgraph of some calG graph on the same vertex set (+extra vertices)? brute force over supersets
    n=G.number_of_nodes()+extra
    H0=nx.Graph(); H0.add_nodes_from(range(n)); H0.add_edges_from(G.edges())
    non=[e for e in itertools.combinations(range(n),2) if not H0.has_edge(*e)]
    for r in range(len(non)+1):
        for add in itertools.combinations(non,r):
            H=H0.copy(); H.add_edges_from(add)
            if in_calG(H): return True
    return False
for n in range(1,6):
    gs=[G for G in graph_atlas_g() if G.number_of_nodes()==n]
    exc=[G for G in gs if not structural(G)]
    bad=[G for G in gs if structural(G)!=in_calG(G)]
    bad2=[G for G in exc if closure_calG_bruteforce(G,0) or closure_calG_bruteforce(G,1)]
    print(n,len(gs),"exceptional",len(exc),"struct!=calG",len(bad),"exceptional-but-in-closure(<=1 extra vertex)",len(bad2))
    if n==5:
        for G in exc: print(sorted(G.edges()), sorted(d for _,d in G.degree()))

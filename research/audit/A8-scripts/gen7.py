# Produce all 1044 graphs on 7 vertices (networkx atlas), with structural flags.
import networkx as nx, itertools, sys
from networkx.generators.atlas import graph_atlas_g
IDX={}
k=0
for i in range(7):
    for j in range(i+1,7):
        IDX[(i,j)]=k; k+=1
def mask(G):
    m=0
    for u,v in G.edges():
        a,b=min(u,v),max(u,v); m|=1<<IDX[(a,b)]
    return m
def triangles(G):
    return [t for t in itertools.combinations(G.nodes(),3) if G.has_edge(t[0],t[1]) and G.has_edge(t[0],t[2]) and G.has_edge(t[1],t[2])]
def has_triangle_pair(G):
    T=triangles(G)
    for s,t in itertools.combinations(T,2):
        if len(set(s)&set(t))==1: return True
    return False
def blocks(G):
    # biconnected components as vertex sets, plus isolated/bridge handled by nx
    return [set(c) for c in nx.biconnected_components(G)]
def block_maxdeg(G):
    md=0
    for B in blocks(G):
        H=G.subgraph(B)
        md=max(md,max(d for _,d in H.degree()))
    return md
def structural(G):  # FHZ hypothesis: no triangle pair, every block max degree <= 3
    return (not has_triangle_pair(G)) and block_maxdeg(G)<=3
def in_calG(G):  # Botler-Sambinelli family (G itself, not closure)
    if block_maxdeg(G)>3: return False
    for C in nx.connected_components(G):
        H=G.subgraph(C)
        if max((d for _,d in H.degree()),default=0)<=3: continue
        tb=0
        for B in blocks(H):
            if len(B)>=3 and triangles(G.subgraph(B)): tb+=1
        if tb>1: return False
    return True
gs=[G for G in graph_atlas_g() if G.number_of_nodes()==7]
print(len(gs),file=sys.stderr)
ns=0; nc=0; both=0
with open('g7.txt','w') as f:
    for G in gs:
        s=structural(G); c=in_calG(G)
        ns+=s; nc+=c; both+= (s and c)
        f.write(f"{mask(G)} {int(s)} {int(c)}\n")
print("structural",ns,"calG",nc,"both",both,"calG-not-structural",nc-both,file=sys.stderr)

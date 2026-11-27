import itertools, sys
sys.path.insert(0, sys.argv[1])
import networkx as nx
from verify3 import lovasz_decomps, predicate, end_map
# J = K_{3,4} + x1x2 ; z = x3
X=['r','rp']; Y=['y1','y2','y3','y4','y5','y6']
J=nx.Graph([(x,y) for x in X for y in Y]+[('z',v) for v in X+Y])
J=nx.convert_node_labels_to_integers(J, label_attribute='name')
name={v:J.nodes[v]['name'] for v in J}; idx={name[v]:v for v in J}
z=idx['z']; N=sorted(J.neighbors(z))
def forest_tjoins(H,T):
    E=list(H.edges())
    for s in range(1,len(E)+1):
        for S in itertools.combinations(E,s):
            F=nx.Graph(S)
            if not nx.is_forest(F): continue
            if {v for v in F if F.degree(v)%2}==set(T): yield S
def rootings(S, w):
    F=nx.Graph(S); comps=[sorted(c) for c in nx.connected_components(F)]
    choices=[[w] if w in c else c for c in comps]
    for roots in itertools.product(*choices):
        par={}
        for c,rt in zip(comps,roots):
            for u,v in nx.bfs_tree(F.subgraph(c),rt).edges(): par[v]=u
        yield par
for r in N:
    ok=None
    for w in N:
        if w==r: continue
        T=[u for u in N if u not in (r,w)]
        H=J.copy(); H.remove_nodes_from([z,r])
        for S in forest_tjoins(H,T):
            M=J.copy(); M.remove_edges_from([(z,w)]+[(z,v) for v in T]+list(S))
            if M.degree(w)==0: M.remove_node(w)
            decs=lovasz_decomps(M, cap=100000)
            for par in rootings(S,w):
                for D in decs:
                    if predicate(D,par):
                        ok=(name[w],[(name[a],name[b]) for a,b in S],{name[a]:name[b] for a,b in par.items()},[[name[x] for x in p] for p in D]); break
                if ok: break
            if ok: break
        if ok: break
    print("root",name[r],"FOREST BASE" if ok else "NONE", ok)

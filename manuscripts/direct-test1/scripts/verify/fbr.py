"""Generalised forest lift: Phi a forest T-join of J - z (r allowed, r not in T), r and w roots.
Exhaustive search for a base; executes the lift and verifies Test1 independently."""
import itertools, sys
sys.path.insert(0, sys.argv[1])
import networkx as nx
from verify3 import lovasz_decomps, predicate, end_map, append_and_check
def forest_tjoins(H,T):
    E=list(H.edges())
    for s in range(1,len(E)+1):
        for S in itertools.combinations(E,s):
            F=nx.Graph(S)
            if not nx.is_forest(F): continue
            if {v for v in F if F.degree(v)%2}==set(T): yield S
def rootings(S, forced):
    F=nx.Graph(S); comps=[sorted(c) for c in nx.connected_components(F)]
    choices=[]
    for c in comps:
        fc=[x for x in forced if x in c]
        if len(fc)>1: return
        choices.append(fc if fc else c)
    for roots in itertools.product(*choices):
        par={}
        for c,rt in zip(comps,roots):
            for u,v in nx.bfs_tree(F.subgraph(c),rt).edges(): par[v]=u
        yield par
def lift(J,z,r,D0,par,k):
    paths=[list(p) for p in D0]
    iz=[i for i,p in enumerate(paths) if p[0]==z or p[-1]==z]; P=paths[iz[0]]
    if P[-1]==z: P.reverse()
    if len(P)>=3: paths[iz[0]]=P[1:]
    else:
        del paths[iz[0]]
        for i,Q in enumerate(paths):
            if r in Q[1:-1]:
                j=Q.index(r); paths[i:i+1]=[Q[:j+1],Q[j:]]; break
    B=J.copy(); B.remove_node(z)
    return append_and_check(B,paths,par,k,r=r,need_r=2)
def run(J,z,label=lambda v:v):
    k=(J.number_of_nodes()-1)//2; N=sorted(J.neighbors(z)); out={}
    for r in N:
        res=None
        for w in N:
            if w==r: continue
            T=[u for u in N if u not in (r,w)]
            H=J.copy(); H.remove_node(z)
            for S in forest_tjoins(H,T):
                M=J.copy(); M.remove_edges_from([(z,w)]+[(z,v) for v in T]+list(S))
                Mw=M.copy()
                if Mw.degree(w)==0: Mw.remove_node(w)
                decs=None
                for par in rootings(S,[x for x in (r,w) if x in nx.Graph(S)]):
                    if decs is None: decs=lovasz_decomps(Mw,cap=200000)
                    for D in decs:
                        if predicate(D,par):
                            assert lift(J,z,r,D,par,k), "LIFT FAIL"
                            res=(label(w),[(label(a),label(b)) for a,b in S],[[label(x) for x in p] for p in D]); break
                    if res: break
                if res: break
            if res: break
        out[label(r)]=res
        print("root",label(r),"BASE" if res else "NONE",res,flush=True)
    return out
if __name__=="__main__":
    X=['r','rp']; Y=['y%d'%i for i in range(1,7)]
    J=nx.Graph([(x,y) for x in X for y in Y]+[('z',v) for v in X+Y])
    J=nx.convert_node_labels_to_integers(J,label_attribute='name')
    nm={v:J.nodes[v]['name'] for v in J}; z=[v for v in J if nm[v]=='z'][0]
    run(J,z,lambda v:nm[v])

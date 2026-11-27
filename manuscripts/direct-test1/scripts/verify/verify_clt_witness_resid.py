"""Independent check of clt's residual-graph triangle-base witnesses (B graph6, z = |B| joined to 0..5)."""
import sys
sys.path.insert(0, sys.argv[1])
import networkx as nx
from dtl import lift, verify
B=nx.from_graph6_bytes(sys.argv[2].encode()); nB=B.number_of_nodes(); z=nB
J=B.copy(); J.add_edges_from((z,u) for u in range(6))
assert [v for v in J if J.degree(v)%2==0]==[z]
# relabel so that z = 0 for dtl.lift/verify (which assume z = 0)
perm={z:0}; perm.update({v:v+1 for v in range(nB)})
J0=nx.relabel_nodes(J,perm)
blocks=open(sys.argv[3]).read().split("FOUND")[1:]
for blk in blocks:
    lines=blk.strip().split("\n"); head=lines[0]
    if "z=%d"%z not in head: continue
    r=int(head.split("r=")[1].split()[0]); w=int(head.split("w=")[1].split()[0])
    pairs=eval(head.split("pairs=")[1].split(" orient")[0])
    D0=[[perm[int(x)] for x in l.split()] for l in lines[1:] if l.strip()]
    r0,w0=perm[r],perm[w]; pr=[(perm[a],perm[b]) for a,b in pairs]
    M=J0.copy(); M.remove_edges_from([(0,w0)]+[(0,x) for p in pr for x in p]+pr)
    used=set(); ends={v:0 for v in M}
    for P in D0:
        assert len(set(P))==len(P)
        for x,y in zip(P,P[1:]):
            e=frozenset((x,y)); assert M.has_edge(x,y) and e not in used; used.add(e)
        ends[P[0]]+=1; ends[P[-1]]+=1
    assert len(used)==M.number_of_edges() and all(ends[v]==M.degree(v)%2 for v in M)
    Q={}
    for P in D0: Q[P[0]]=P; Q[P[-1]]=P
    disj=all((b not in Q[a]) or (a not in Q[b]) for a,b in pr)
    res=lift(J0,J0.number_of_nodes(),r0,w0,pr,D0)
    print("B-root",r,"w",w,"pairs",pairs,"Lovasz ok, disjunctions",disj,"lift+Test1",res is not None and verify(J0,J0.number_of_nodes(),r0,res))

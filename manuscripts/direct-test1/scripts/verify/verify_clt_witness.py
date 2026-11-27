"""Independent check of a triangle-base witness: D0 Lovász decomposition of M with the
disjunctions; then execute the lift (dtl.lift) and verify Test1 (dtl.verify)."""
import ast, sys  # usage: verify_clt_witness.py DIR_WITH_dtl.py nobase_budget.txt triangle_base_witnesses.txt
sys.path.insert(0, sys.argv[1])
import networkx as nx
from dtl import lift, verify
line=[l for l in open(sys.argv[2]) if l.startswith("NO BASE 15")][0]
E=ast.literal_eval("["+line.split("[",1)[1].rsplit("]",1)[0]+"]"); r=int(line.rsplit("r",1)[1])
J=nx.Graph(E); n=J.number_of_nodes(); z=[v for v in J if J.degree(v)%2==0]; assert z==[0], z
w=2; pairs=[(3,4),(5,6)]; orient=(0,0)
W=open(sys.argv[3]).read().split("FOUND")[1].strip().split("\n")[1:]
D0=[list(map(int,l.split())) for l in W if l.strip()]
M=J.copy(); M.remove_edges_from([(0,w)]+[(0,x) for p in pairs for x in p]+pairs)
used=set(); ends={v:0 for v in M}
for P in D0:
    assert len(set(P))==len(P) and len(P)>=2
    for x,y in zip(P,P[1:]):
        e=frozenset((x,y)); assert M.has_edge(x,y) and e not in used; used.add(e)
    ends[P[0]]+=1; ends[P[-1]]+=1
assert len(used)==M.number_of_edges()
assert all(ends[v]==M.degree(v)%2 for v in M), "not Lovasz"
Q={P[0]:P for P in D0}; Q.update({P[-1]:P for P in D0})
for (a,b),o in zip(pairs,orient):
    c,x=(b,a) if o==0 else (a,b)  # orient 0: Q(b) avoids a (clt: c,x=(a,b) means path at a avoids b?)
    print("pair",(a,b),"Q(a) avoids b:",b not in Q[a],"Q(b) avoids a:",a not in Q[b])
res=lift(J,n,r,w,pairs,D0)
print("lift:", res is not None and verify(J,n,r,res), "r =",r, "n =",n, "m =",J.number_of_edges())

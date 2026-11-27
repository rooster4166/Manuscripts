"""Independent check of tb_ls.py output for 'NO BASE n [edges] r R' lines: D0 Lovász on M, the
disjunctions, then the executed lift (dtl.lift) and Test1 (dtl.verify). usage: vw_gen.py DIR NOBASEFILE LINE TBLS_OUTPUT"""
import ast, sys
sys.path.insert(0, sys.argv[1])
import networkx as nx
from dtl import lift, verify
line=open(sys.argv[2]).read().split("\n")[int(sys.argv[3])]
E=ast.literal_eval("["+line.split("[",1)[1].rsplit("]",1)[0]+"]"); r=int(line.rsplit("r",1)[1])
J=nx.Graph(E); n=J.number_of_nodes(); assert [v for v in J if J.degree(v)%2==0]==[0]
txt=open(sys.argv[4]).read(); assert "FOUND" in txt
head,*rest=txt.split("FOUND",1)[1].strip().split("\n")
assert int(head.split("r=")[1].split()[0])==r
w=int(head.split("w=")[1].split()[0]); pairs=eval(head.split("pairs=")[1].split(" orient")[0])
D0=[list(map(int,l.split())) for l in rest if l.strip() and l.split()[0].isdigit()]
M=J.copy(); M.remove_edges_from([(0,w)]+[(0,x) for p in pairs for x in p]+pairs)
used=set(); ends={v:0 for v in M}
for P in D0:
    assert len(set(P))==len(P) and len(P)>=2
    for x,y in zip(P,P[1:]):
        e=frozenset((x,y)); assert M.has_edge(x,y) and e not in used; used.add(e)
    ends[P[0]]+=1; ends[P[-1]]+=1
assert len(used)==M.number_of_edges() and all(ends[v]==M.degree(v)%2 for v in M)
Q={}
for P in D0: Q[P[0]]=P; Q[P[-1]]=P
assert all((b not in Q[a]) or (a not in Q[b]) for a,b in pairs)
res=lift(J,n,r,w,pairs,D0); ok=res is not None and verify(J,n,r,res)
print("line",sys.argv[3],"m",J.number_of_edges(),"r",r,"VERIFIED" if ok else "LIFT FAIL",flush=True)

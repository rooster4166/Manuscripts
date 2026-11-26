import sys, networkx as nx
sys.path.insert(0,'/home/user/Manuscripts/tools')
from pathnum import solve
bad=0;n=0
for line in open('xval2.txt'):
    g,r,m,v=line.split(); r=int(r); m=int(m); v=int(v)
    G=nx.from_graph6_bytes(g.encode())
    res=solve(G,min_ends={r:m},workers=1)
    n+=1
    if res.value!=v: bad+=1; print('MISMATCH',g,r,m,v,res.value)
print('checked',n,'mismatches',bad)

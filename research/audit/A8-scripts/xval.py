import sys, networkx as nx
sys.path.insert(0,'/home/user/Manuscripts/tools')
from pathnum import solve
bad=0; n=0
for line in open('pn67.txt'):
    g,v=line.split(); G=nx.from_graph6_bytes(g.encode())
    r=solve(G,workers=1)
    n+=1
    if r.value!=int(v): bad+=1; print('MISMATCH',g,v,r.value)
print('checked',n,'mismatches',bad)

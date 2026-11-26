import networkx as nx, itertools, sys
sys.path.insert(0,'/home/user/Manuscripts/tools')
from pathnum import verify_partition
J=nx.complete_graph(6); J.remove_edges_from([(0,2),(2,3),(1,3)])
print('K6-{02,23,13} degrees',dict(J.degree()), '3-conn', nx.node_connectivity(J))
rows=[(1,0,3,4,5),(1,2,4,0,5,3),(2,5,1,4)]
print(' rows partition J:',verify_partition(J,rows))
B=J.copy(); B.remove_node(0)
dele=[(1,2,4,5),(1,5),(1,4,3,5,2)]
print(' deletion partition of J-0:',verify_partition(B,dele),'ends at 1:',sum((P[0]==1)+(P[-1]==1) for P in dele),'|J|/2=',3)
E="04, 05, 15, 45, 06, 26, 36, 07, 17, 27, 37, 67, 08, 18, 28, 38, 48, 68, 78"
J=nx.Graph([tuple(int(c) for c in e.strip()) for e in E.split(',')])
print('9-vertex example: n',J.number_of_nodes(),'even',[v for v in J if J.degree(v)%2==0],'kappa',nx.node_connectivity(J))
z=7; K=J.subgraph([v for v in J[z] if v!=1]); print(' K universal',[v for v in K if K.degree(v)==len(K)-1], 'K edges',sorted(K.edges()))
rows=[(0,8,6,2,7,1,5),(4,5,0,6,3,8,2),(6,7,8),(3,7,0,4,8,1)]
print(' rows partition J:',verify_partition(J,rows))
term=set()
for P in rows:
    for i,x in enumerate(P):
        if x==z:
            if i==0: term.add(P[1])
            if i==len(P)-1: term.add(P[-2])
print(' terminal neighbours of 7:',sorted(term))
B=J.copy(); B.remove_node(z)
pieces=[]
for P in rows:
    cur=[]
    for x in P:
        if x==z:
            if len(cur)>=2: pieces.append(tuple(cur))
            cur=[]
        else: cur.append(x)
    if len(cur)>=2: pieces.append(tuple(cur))
print(' after deleting 7:',pieces,len(pieces),'paths; ends at 1:',sum((P[0]==1)+(P[-1]==1) for P in pieces),' partition ok',verify_partition(B,pieces))

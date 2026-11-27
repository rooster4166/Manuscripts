"""A29: filter nauty-geng output to graphs with exactly one even vertex; prints the count."""
import sys, networkx as nx
cnt=0; out=open(sys.argv[1],'w')
for line in sys.stdin:
    line=line.strip()
    if not line: continue
    G=nx.from_graph6_bytes(line.encode())
    ev=[v for v in G if G.degree(v)>0 and G.degree(v)%2==0]
    if len(ev)==1:
        cnt+=1; out.write(line+'\n')
print(cnt)

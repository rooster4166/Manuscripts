import sys, networkx as nx
# keep B with exactly 6 even vertices, all even degrees >= 6, min degree >= 5, and some r in S with K=B[S-r] having >=2 universal
out=open(sys.argv[2],'w'); kept=0
for line in open(sys.argv[1]):
    B=nx.from_graph6_bytes(line.strip().encode())
    S=[v for v in B if B.degree(v)%2==0]
    if len(S)!=6: continue
    if min(B.degree(v) for v in S)<6 or min(d for _,d in B.degree())<5: continue
    good=False
    for r in S:
        T=[x for x in S if x!=r]; K=B.subgraph(T)
        if sum(1 for x in T if K.degree(x)==4)>=2: good=True
    if good: out.write(line); kept+=1
print('kept',kept)

import sys, networkx as nx
from collections import Counter
for fn in sys.argv[1:]:
  for line in open(fn):
    s=line.split()[0]
    J=nx.from_graph6_bytes(s.encode())
    n=J.number_of_nodes(); k=(n-1)//2
    z=[v for v in J if J.degree(v)%2==0][0]
    Z=set(J[z]); B=J.copy(); B.remove_node(z)
    T=set(B)-Z
    for r in sorted(Z):
        if J.degree(r)!=n-2: continue
        s_=[v for v in B if v!=r and not B.has_edge(r,v)][0]
        G=B.copy(); G.remove_node(r)
        EG=[v for v in G if G.degree(v)%2==0 and G.degree(v)>0]
        degJ=sorted((J.degree(x) for x in B), reverse=True)
        print(fn.split('/')[-1], s, r, 'n',n,'k',k,'s in Z' if s_ in Z else 's in T', '|T|',len(T), '|EG|',len(EG),
              '#n-2:',sum(1 for d in degJ if d==n-2), 'mindegB', min(dict(B.degree()).values()), 'm(B)',B.number_of_edges(), 'degJ', degJ)

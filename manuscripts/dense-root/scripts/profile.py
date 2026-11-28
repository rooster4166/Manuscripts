import sys, networkx as nx
from collections import Counter
fn=sys.argv[1]
C=Counter(); tot=0
for line in open(fn):
    s=line.split()[0]
    J=nx.from_graph6_bytes(s.encode())
    n=J.number_of_nodes(); k=(n-1)//2
    ev=[v for v in J if J.degree(v)%2==0]; z=ev[0]
    Z=set(J[z]); B=J.copy(); B.remove_node(z)
    T=set(B)-Z
    for r in sorted(Z):
        if J.degree(r)!=n-2: continue
        tot+=1
        s_=[v for v in B if v!=r and not B.has_edge(r,v)][0]
        sinZ = s_ in Z
        G=B.copy(); G.remove_node(r)
        evG=[v for v in G if G.degree(v)%2==0]
        degsN=sorted((J.degree(x) for x in G if x!=s_), reverse=True)
        hk = sum(1 for d in degsN if d>=n-2)
        TinN = T - {s_}
        tadj = (len(T)==2 and B.has_edge(*list(T)))
        C[('sinZ' if sinZ else 'snotZ', len(evG), 'tadj' if tadj else 'tnonadj', 'h(n-2)=%d'%hk)]+=1
print(tot)
for k,v in sorted(C.items()): print(k,v)

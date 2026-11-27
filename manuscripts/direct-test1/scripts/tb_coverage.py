"""tb_coverage.py: how many roots the proved cases of TriangleBase.lean reach (packed / far-apart, L1*), 3-connected J of order 7 and 9 (session claude/triangle-base). Run from scripts/."""
import networkx as nx, itertools, sys
sys.path.insert(0,'.')
from tb import data_choices, base_graph, even_vertex
from collections import Counter
C=Counter()
for n in (7,9):
  for l in open(f'../../stl/scripts/one_even_{n}.g6'):
    J=nx.from_graph6_bytes(l.strip().encode()); z=even_vertex(J)
    if z is None or J.degree(z)<4: continue
    if nx.node_connectivity(J)<3: continue
    m=J.degree(z)//2
    for r in J[z]:
        ch=list(data_choices(J,z,r))
        if not ch: continue
        C[(m,'roots')]+=1
        packed=False; l1=False
        for w,pairs in ch:
            M=base_graph(J,z,w,pairs)
            X=[v for p in pairs for v in p]
            ok=all(not M.has_edge(x,y) and not (set(M[x])&set(M[y])) for x,y in itertools.combinations(X,2))
            packed|=ok
            if m==2:
                a,b=pairs[0]
                l1 |= (not J.has_edge(w,a)) or (not J.has_edge(w,b))
        C[(m,'packed')]+=packed
        if m==2: C[(m,'L1*')]+=l1; C[(m,'packed_or_L1*')]+= (packed or l1)
for k in sorted(C): print(k,C[k])

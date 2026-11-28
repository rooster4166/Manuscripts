import sys, networkx as nx
exec(open('thm_cov.py').read().split("C = Counter()")[0])
exec("\n".join(open("thm_cov.py").read().split("# ---- extended")[1].split("C2 = Counter()")[0].split("\n")[1:]))
cnt=0
for line in open('/home/user/Manuscripts/manuscripts/multi-token/data/J9_d6.g6'):
    g6=line.split()[0]
    J=nx.from_graph6_bytes(g6.encode()); n=J.number_of_nodes(); k=(n-1)//2
    z=[v for v in J if J.degree(v)%2==0][0]; Z=set(J[z]); B=J.copy(); B.remove_node(z)
    for r in sorted(Z):
        if J.degree(r)!=n-2: continue
        s=[v for v in B if v!=r and not B.has_edge(r,v)][0]
        a=thmA(B,r,s,k); b=thmB2(B,r,s,k,Z)
        if a is True or b is True or mr47(B,k) or mr74(B,k) or mr166(B,r,k,Z): continue
        T=[v for v in B if v not in Z]
        G=B.copy(); G.remove_node(r)
        cnt+=1
        if cnt<=25:
            print(g6, r, 'sinZ' if s in Z else 'snotZ', 'b=',b, 'T',T, 'dJ(T)',[J.degree(t) for t in T], 'dJ(s)',J.degree(s),
              'dJ(N-T)', sorted([J.degree(x) for x in B if x not in T and x not in (r,s)],reverse=True),
              'dist_G(t1,t2)', nx.shortest_path_length(G,T[0],T[1]) if s in Z else '-')
print(cnt)

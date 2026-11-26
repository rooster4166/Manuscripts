import itertools, networkx as nx
exec(open('tables.py').read().split("def fe(s)")[0])
# Thm 123 t=2 and t=3 conditions on all exceptional shapes
bad=[]
for S in ['K0','K1','K2','K3','M','P','C']:
    G=shape(S); univ=[x for x in G if G.degree(x)==4]
    for C in itertools.combinations('abcde',2):
        ok=any(len(set(G[x])-set(C))>=2 for x in C)
        if not ok: bad.append((S,'t=2',C))
    for C in itertools.combinations('abcde',3):
        u,v=[x for x in 'abcde' if x not in C]
        ok=G.has_edge(u,v) or any(h in C and G.has_edge(u,h) and G.has_edge(h,v) for h in univ)
        if not ok: bad.append((S,'t=3',C))
print('Thm123 t=2/t=3 condition failures (expected: only M with contacts bc or de at t=2):',bad)
# Thm 132 example: square of odd cycle, explicit Hamilton paths from text
def sq(m):
    K=nx.Graph(); K.add_nodes_from(range(m))
    for i in range(m): K.add_edge(i,(i+1)%m); K.add_edge(i,(i+2)%m)
    return K
def text_path(m,j):
    if j==1: return [0]+list(range(m-1,0,-1))
    P=[0]+list(range(m-1,j,-1))   # 0, m-1, ..., j+1
    x=j+1
    desc=[]
    y=x-2
    while y>=1: desc.append(y); y-=2
    P+=desc
    last=desc[-1]; other=3-last
    asc=list(range(other,j+1,2))
    P+=asc
    return P
badm=[]
for m in range(5,62,2):
    K=sq(m)
    for j in range(1,(m-1)//2+1):
        P=text_path(m,j)
        okpath = sorted(P)==list(range(m)) and all(K.has_edge(P[i],P[i+1]) for i in range(m-1)) and P[0]==0 and P[-1]==j
        R=K.copy(); R.remove_edges_from(zip(P,P[1:]))
        okres = nx.is_connected(R) or not any(nx.triangles(R).values())
        if not (okpath and okres): badm.append((m,j,okpath,okres))
    if max(dict(K.degree()).values())>4: badm.append((m,'deg'))
print('Thm 132 example failures for m=5..61:',badm)

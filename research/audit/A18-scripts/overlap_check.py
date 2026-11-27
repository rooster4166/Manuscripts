# Independent brute-force check of the overlap counterexample in E21(C).
import itertools, sys
def g6(s):
    n=ord(s[0])-63; bits=[]
    for ch in s[1:]:
        v=ord(ch)-63
        bits += [(v>>(5-i))&1 for i in range(6)]
    K={v:set() for v in range(n)}; k=0
    for j in range(1,n):
        for i in range(j):
            if bits[k]: K[i].add(j); K[j].add(i)
            k+=1
    return K
K=g6("K??FEaKR@oE_")
pairs0=[(0,9),(0,10),(1,8),(1,11),(2,7),(2,8),(2,9),(3,6),(3,8),(3,9),(4,6),(4,7),(4,11),(5,6),(5,7),(5,10)]
pairs=eval(sys.argv[1]) if len(sys.argv)>1 else pairs0
n=len(K); assert all(len(K[v])==3 for v in K)
def bfs(s):
    d={s:0}; fr=[s]
    while fr:
        nf=[]
        for x in fr:
            for y in K[x]:
                if y not in d: d[y]=d[x]+1; nf.append(y)
        fr=nf
    return d
D=[bfs(v) for v in range(n)]
print("min pair distance", min(D[a][b] for a,b in pairs))
# can the 16 pairs be covered as union of 3 perfect pairings?
P=set(pairs)
def perfect_matchings(E, V):
    if not V: yield []; return
    v=min(V)
    for (a,b) in E:
        if v in (a,b):
            w=b if a==v else a
            if w in V:
                for m in perfect_matchings(E, V-{v,w}): yield [(a,b)]+m
pms=list(perfect_matchings(sorted(P), frozenset(range(n))))
print("perfect pairings inside the pair set:", len(pms))
ok3=any(set(a)|set(b)|set(c)==P for a in pms for b in pms for c in pms)
print("union of three perfect pairings:", ok3)
# brute force over end-edge choices
nbr={v:sorted(K[v]) for v in K}
found=0
for ch in itertools.product(range(3), repeat=n):
    # at v, end edge = nbr[v][ch[v]]; the other two neighbours are linked through v
    nxt={}  # (v, w) -> next vertex after traversing edge w->v through v
    for v in range(n):
        a,b=[w for i,w in enumerate(nbr[v]) if i!=ch[v]]
        nxt[(a,v)]=b; nxt[(b,v)]=a
    # trace paths starting at end edges
    seen=set(); good=True; paths=[]
    for v in range(n):
        w=nbr[v][ch[v]]
        e=frozenset((v,w))
        if e in seen: continue
        path=[v,w]; prev,cur=v,w; seen.add(e)
        while (prev,cur) in nxt:
            nx=nxt[(prev,cur)]; seen.add(frozenset((cur,nx)))
            path.append(nx); prev,cur=cur,nx
        if len(set(path))!=len(path): good=False; break
        paths.append(path)
    if not good: continue
    if len(seen)!=3*n//2: continue  # some edges on cycles
    if all(not (a in set(p) and b in set(p)) for p in paths for a,b in pairs):
        found+=1; print("separating:", paths); break
print("separating decompositions found:", found)

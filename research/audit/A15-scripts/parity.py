import random, itertools
random.seed(1)
def rand_graph(n,p):
    E={(i,j) for i in range(n) for j in range(i+1,n) if random.random()<p}
    adj={v:set() for v in range(n)}
    for i,j in E: adj[i].add(j); adj[j].add(i)
    return adj
bad=0; tested=0
for trial in range(3000):
    n=random.randint(3,11); adj=rand_graph(n,random.uniform(0.3,0.9))
    deg={v:len(adj[v]) for v in adj}
    for r in adj:
        Ev={v for v in adj if deg[v]%2==0}; S=Ev|{r}
        dJ={v:deg[v]+(1 if v in S else 0) for v in adj}; dz=len(S)
        evJ={v for v in adj if dJ[v]%2==0}|({'z'} if dz%2==0 else set())
        if n%2==0 and deg[r]%2==0:
            tested+=1
            if evJ!={'z'}: bad+=1
        if n%2==1 and deg[r]%2==1:
            tested+=1
            if evJ!={'z',r}: bad+=1
print("apex parity: tested",tested,"bad",bad)
# Lemma 6.2(c): |C| + [dA(x) odd] + [dA(y) odd] even when all of C odd in B
bad=0; tested=0
for trial in range(20000):
    n=random.randint(4,10); adj=rand_graph(n,random.uniform(0.2,0.8))
    deg={v:len(adj[v]) for v in adj}
    x,y=random.sample(range(n),2)
    rest=[v for v in adj if v not in (x,y)]
    # components of B-{x,y}
    seen=set()
    for s in rest:
        if s in seen: continue
        comp={s}; st=[s]
        while st:
            u=st.pop()
            for w in adj[u]:
                if w not in (x,y) and w not in comp: comp.add(w); st.append(w)
        seen|=comp
        if len(comp)==len(rest): continue
        if all(deg[c]%2==1 for c in comp):
            tested+=1
            dA={v:sum(1 for w in adj[v] if w in comp or v in comp or {v,w}=={x,y}) for v in (x,y)}
            if (len(comp)+dA[x]%2+dA[y]%2)%2: bad+=1
print("port parity: tested",tested,"bad",bad)

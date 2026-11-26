import itertools, sys
def cycles_in_complete(n, forbidden):
    """all simple cycles of K_n (as frozenset of edges, plus vertex tuple) avoiding forbidden edges"""
    out=[]
    for L in range(3,n+1):
        for verts in itertools.combinations(range(n),L):
            first=verts[0]; rest=verts[1:]
            for perm in itertools.permutations(rest):
                if perm[0]>perm[-1]: continue
                cyc=(first,)+perm
                es=frozenset(frozenset((cyc[i],cyc[(i+1)%L])) for i in range(L))
                if es & forbidden: continue
                out.append((cyc,es))
    return out
for n in range(5,9):
    P=[0,1,2,3]
    forb=frozenset(frozenset((P[i],P[i+1])) for i in range(3))
    cs=[c for c in cycles_in_complete(n,forb) if set(c[0])&set(P)]
    print(n,len(cs))

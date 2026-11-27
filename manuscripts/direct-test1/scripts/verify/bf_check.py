import itertools, random, sys
import networkx as nx
sys.path.insert(0, '.')
from verify3 import lovasz_decomps

def brute(G):
    nodes=list(G); paths=[]
    for s,t in itertools.combinations(nodes,2):
        for p in nx.all_simple_paths(G,s,t):
            paths.append(tuple(p))
    E={frozenset(e) for e in G.edges()}
    pe=[frozenset(frozenset(x) for x in zip(p,p[1:])) for p in paths]
    b={v:G.degree(v)%2 for v in nodes}
    res=set()
    def rec(rem, ends, chosen):
        if not rem:
            if all(ends[v]==b[v] for v in nodes):
                res.add(frozenset(chosen))
            return
        e=min(rem, key=lambda x: tuple(sorted(x)))
        for i,p in enumerate(paths):
            if e in pe[i] and pe[i]<=rem:
                a,c=p[0],p[-1]
                if ends[a]+1>b[a] or ends[c]+1>b[c]: continue
                ends[a]+=1; ends[c]+=1
                rec(rem-pe[i], ends, chosen+[pe[i]])
                ends[a]-=1; ends[c]-=1
    rec(E,{v:0 for v in nodes},[])
    return len(res)

rng=random.Random(3); tested=0; bad=0
while tested<60:
    n=rng.choice([4,5,6,7]); G=nx.gnp_random_graph(n,rng.uniform(0.4,0.8),seed=rng.randrange(10**9))
    if not nx.is_connected(G) or G.number_of_edges()>10: continue
    ev=[v for v in G if G.degree(v)%2==0 and G.degree(v)>0]
    if len(ev)>1: continue
    a=len({frozenset(frozenset(zip(p,p[1:])) and frozenset(frozenset(x) for x in zip(p,p[1:]))) for p in []}) # noop
    mine={frozenset(frozenset(frozenset(x) for x in zip(p,p[1:])) for p in D) for D in lovasz_decomps(G,cap=10**6)}
    br=brute(G); tested+=1
    if len(mine)!=br: bad+=1; print("MISMATCH",sorted(G.edges()),len(mine),br)
print("tested",tested,"mismatches",bad)

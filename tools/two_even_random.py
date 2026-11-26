"""Random check of Conjecture 31 (endpoint-structure): 2-connected graphs with exactly two even
vertices and no universal odd vertex are tight. Usage: two_even_random.py n seed count pmin pmax"""
# random sanity check of Conjecture 31 at n=10: 2-connected, exactly two even vertices,
# no universal odd vertex  =>  tight
import sys, random, networkx as nx
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from pathnum2 import decompose
random.seed(int(sys.argv[2]) if len(sys.argv)>2 else 7)
n=int(sys.argv[1]); tested=0; fails=0; tries=0
N=int(sys.argv[3]) if len(sys.argv)>3 else 30
while tested<N:
    tries+=1
    p=random.uniform(float(sys.argv[4]),float(sys.argv[5]))
    G=nx.gnp_random_graph(n,p,seed=random.randrange(10**9))
    if not nx.is_connected(G) or nx.node_connectivity(G)<2: continue
    ev=[v for v in G if G.degree(v)%2==0]
    if len(ev)!=2: continue
    if any(G.degree(w)%2 and G.degree(w)==n-1 for w in G): continue
    tested+=1
    ex={v:(G.degree(v)%2) for v in G}
    st,paths=decompose(G,(n-2)//2,exact_ends=ex,time_limit=300,workers=1)
    ok = paths is not None
    print(tested, nx.to_graph6_bytes(G,header=False).decode().strip(), 'm=',G.number_of_edges(), st, flush=True)
    if not ok: fails+=1
print('n',n,'tested',tested,'fails',fails)

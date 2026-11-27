import networkx as nx, itertools, sys
P = nx.petersen_graph()
LG = nx.line_graph(P)                       # 15 vertices, 30 edges, 4-regular
LG = nx.convert_node_labels_to_integers(LG)
assert LG.number_of_nodes()==15 and LG.number_of_edges()==30 and all(d==4 for _,d in LG.degree())
# (1) L(P) has no decomposition into two edge-disjoint Hamiltonian cycles
def ham_cycles(G):
    n=G.number_of_nodes(); start=0; out=[]
    def dfs(path, used):
        u=path[-1]
        if len(path)==n:
            if G.has_edge(u,start): out.append(path[:])
            return
        for w in G[u]:
            if w not in used:
                used.add(w); path.append(w); dfs(path, used); path.pop(); used.remove(w)
    dfs([start],{start})
    return out
cyc = ham_cycles(LG)
edgesets=set()
for c in cyc:
    es=frozenset(frozenset((c[i],c[(i+1)%15])) for i in range(15))
    edgesets.add(es)
allE=frozenset(frozenset(e) for e in LG.edges())
decomp=[es for es in edgesets if (allE-es) in edgesets]
print("Hamiltonian cycles of L(P):", len(edgesets), " Hamiltonian decompositions:", len(decomp)//2)
# (2) build G_bad and check cut-feasibility of S = L
w=0; us=sorted(LG[w]); R=[v for v in LG if v!=w]
G=nx.Graph(); G.add_edges_from((a,b) for a,b in LG.edges() if w not in (a,b))
L=[f"l{i}" for i in range(1,15)]
path=["l1"]+[f"l{i}" for i in range(5,15)]+["l2"]
nx.add_path(G,path); G.add_edge("l3","l4")
for i,u in enumerate(us,1): G.add_edge(f"l{i}",u)
n=G.number_of_nodes(); k=n//2
assert n==28 and nx.is_connected(G) and all(d%2==0 for _,d in G.degree())
print("G_bad: n =",n,"m =",G.number_of_edges(),"2-connected:",nx.is_biconnected(G), "degrees", sorted(set(d for _,d in G.degree())))
b={v:(2 if v in L else 0) for v in G}
slack={v:2*k-G.degree(v)-b[v] for v in G}
print("slacks:", sorted(set(slack.values())))
# only W with b(W) - |delta(W)| > 24 can violate; b(W)=2|W∩L| <= 28, so need |W∩L| >= 13
worst=-10**9; viol=0
for drop in [None]+L:
    WL=[x for x in L if x!=drop]
    for r in range(len(R)+1):
        pass
    # enumerate subsets of R via bitmask
    Rl=R
    for mask in range(1<<len(Rl)):
        W=set(WL)|{Rl[i] for i in range(len(Rl)) if mask>>i&1}
        if len(W)==n: continue
        cutW=sum(1 for a,c in G.edges() if (a in W)!=(c in W))
        bW=sum(b[x] for x in W)
        m_out=min(slack[v] for v in G if v not in W)
        ex=bW-cutW-m_out
        worst=max(worst,ex)
        if ex>0: viol+=1
print("max over risky W of b(W)-|delta(W)|-min slack:", worst, " violations:", viol)

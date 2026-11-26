import sys, itertools, random
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
from pathnum2 import decompose
def Ev(G): return [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
def Od(G): return [v for v in G if G.degree(v) % 2 == 1]
def realisable(G, S):
    ex = {v: 1 for v in Od(G)}
    for u in Ev(G): ex[u] = 2 if u in S else 0
    st, P = decompose(G, len(Od(G)) // 2 + len(S), exact_ends=ex, time_limit=60, workers=1)
    return P is not None
G = nx.complete_graph(6); r = 0
for v in (1, 2, 3): G.remove_edge(r, v)
E = Ev(G); print("K6 minus three edges at r: Ev =", E, "G[Ev] edges", list(G.subgraph(E).edges()))
print("  realisable pairs containing r:", [S for S in itertools.combinations(E, 2) if r in S and realisable(G, S)])
# all connected graphs of order <= 7 (even order 4, 6) with G[Ev] = K3 + r
cnt = 0; bad = []
for i, H in enumerate(graph_atlas_g()):
    n = H.number_of_nodes()
    if n % 2 or n < 4 or not nx.is_connected(H): continue
    E = Ev(H)
    if len(E) != 4: continue
    sub = H.subgraph(E)
    iso = [v for v in E if sub.degree(v) == 0]
    if sub.number_of_edges() == 3 and len(iso) == 1:
        cnt += 1; rr = iso[0]
        if not any(realisable(H, S) for S in itertools.combinations(E, 2) if rr in S): bad.append(i)
print("connected even-order graphs (n <= 6) with G[Ev] = K3 + r:", cnt, "; r in no realisable pair:", bad)

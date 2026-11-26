"""Audit A9: exact checks of the small examples in endpoint-structure Secs. 5-6."""
import sys, itertools
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from pathnum2 import decompose
from pathnum import verify_partition

def Ev(G): return [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
def Od(G): return [v for v in G if G.degree(v) % 2 == 1]
def realisable(G, S):
    ex = {v: 1 for v in Od(G)}
    for u in Ev(G): ex[u] = 2 if u in S else 0
    k = len(Od(G)) // 2 + len(S)
    st, P = decompose(G, k, exact_ends=ex, time_limit=60, workers=1)
    if P is not None: assert verify_partition(G, P)
    return P is not None
def pnum(G):
    for k in range(1, G.number_of_edges() + 1):
        st, P = decompose(G, k, time_limit=60, workers=1)
        if P is not None: return k

# 1. Two triangles a x1 x2, b z1 z2 joined by ab (Thm 9 discussion)
G = nx.Graph([('a','x1'),('a','x2'),('x1','x2'),('b','z1'),('b','z2'),('z1','z2'),('a','b')])
E = Ev(G)
print("two triangles: p =", pnum(G), "n/2 =", G.number_of_nodes()//2, "Ev =", sorted(E))
print("   realisable pairs:", [S for S in itertools.combinations(sorted(E), 2) if realisable(G, S)])
# 2. K_{2,4} plus the edge between the two degree-5 vertices
G = nx.complete_bipartite_graph(2, 4); G.add_edge(0, 1)
E = Ev(G)
print("K24+e: Ev =", sorted(E), "degrees", dict(G.degree()))
print("   all pairs realisable:", all(realisable(G, S) for S in itertools.combinations(E, 2)))
# 3. P3 + (K5 - e): no realisable pair contains the middle vertex of P3
K = nx.complete_graph(5); K.remove_edge(0, 1)
G = nx.disjoint_union(nx.path_graph(3), K)
E = Ev(G); y = 1
print("P3+(K5-e): Ev =", sorted(E), "pairs containing y realisable:",
      [S for S in itertools.combinations(sorted(E), 2) if y in S and realisable(G, S)])
# 4. (K5-e) + (K5-e): every realisable set has >= 4 elements; every even vertex has an even neighbour
G = nx.disjoint_union(K, K)
E = Ev(G)
print("2(K5-e): e =", len(E), "realisable 3-sets:", [S for S in itertools.combinations(E, 3) if realisable(G, S)],
      "every even vertex has an even neighbour:", all(any(w in E for w in G[v]) for v in E))
# 5. Thm 7 / Lemma 13 sanity: K6 - PM (all degrees 4, e = 6): Thm 11 says pair step ok etc. (skip)

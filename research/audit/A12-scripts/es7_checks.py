"""Endpoint-structure Section 7: small exact checks (audit A12; A11 exact solver).
  * Remark 54: GsaEDo is critical, and for every a in N_E(7) the pair N_E(7) - a is not
    realisable in G - 7a.
  * Remark 56: all 70 half-sets of M_8 = K_8 minus a perfect matching are realisable (one per orbit
    of 4-sets under Aut, by the number of antipodal pairs contained: 0, 1, 2).
  * Corollary 58 / Prop 64 sanity: edge count of CP(m), 2m(m-1).
"""
import itertools
import networkx as nx
import partitions as pt

G = nx.from_graph6_bytes(b"GsaEDo")
d = dict(G.degree())
NE = sorted(v for v in G[7] if d[v] % 2 == 0)
print("GsaEDo: N(7) =", sorted(G[7]), "N_E(7) =", NE, "e =", sum(1 for v in G if d[v] % 2 == 0),
      "critical:", pt.critical(G))
for a in NE:
    K = G.copy(); K.remove_edge(7, a)
    pair = set(NE) - {a}
    print(f"  a = {a}: pair {sorted(pair)} realisable in G - 7{a}: {pt.realisable(K, pair) is not None}")

M = nx.from_graph6_bytes(b"Gr~v~w")
anti = {0: 3, 3: 0, 1: 2, 2: 1, 4: 5, 5: 4, 6: 7, 7: 6}
reps = {}
for S in itertools.combinations(range(8), 4):
    k = sum(1 for v in S if anti[v] in S) // 2
    reps.setdefault(k, S)
for k, S in sorted(reps.items()):
    P = pt.realisable(M, set(S))
    print(f"M_8: half-set {S} with {k} antipodal pairs realisable: {P is not None}  {P}")
for m in range(2, 8):
    C = nx.complete_graph(2 * m); C.remove_edges_from((2 * i, 2 * i + 1) for i in range(m))
    assert C.number_of_edges() == 2 * m * (m - 1)
print("CP(m) has 2m(m-1) edges for m = 2..7")

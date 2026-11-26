"""Check two elementary facts on all small connected graphs.

(D1) S subset of E is realisable in G  iff  G with a private leaf at each vertex of S
     has a path decomposition with odd(G^S)/2 paths (every odd vertex one end, every
     even vertex internal).
(D2) For every even vertex u, E - {u} is realisable (proof: Lovasz on G + z, z ~ E - u).
"""
import itertools
import sys
import networkx as nx
from faithful_descent import make_oracle
from pathnum import solve


def leaves(G, S):
    H = G.copy()
    for s in S:
        H.add_edge(s, ("leaf", s))
    return H


bad1 = bad2 = tot = 0
for line in open(sys.argv[1]):
    G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(line.strip().encode()))
    E, O, real = make_oracle(G)
    if not E:
        continue
    tot += 1
    for u in E:
        if not real(frozenset(E) - {u}):
            bad2 += 1
            print("D2-FAIL", line.strip(), u, flush=True)
    for k in range(len(E) + 1):
        for S in itertools.combinations(E, k):
            H = leaves(G, S)
            odd = sum(1 for v in H if H.degree(v) % 2)
            r = solve(H, budget=odd // 2, time_limit=60, workers=1)
            tight = r.status in ("OPTIMAL", "FEASIBLE")
            if tight != real(frozenset(S)):
                bad1 += 1
                print("D1-MISMATCH", line.strip(), S, tight, flush=True)
print(f"graphs {tot}; D1 mismatches {bad1}; D2 failures {bad2}")

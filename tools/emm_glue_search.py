"""Search for EMM counterexamples by gluing (missing-move Section 7).

A vertex c of degree 2 with b(c) = 2 is an end of both of its paths, so no path passes through c.
Glue a core (G1, b1) with a leaf c (b1(c) = 1) that is cut-feasible but not realisable to a gadget
(G2, b2) with a leaf c' (b2(c') = 1) that is realisable, identifying c = c'. Then the glued profile
is realisable iff both pieces are, so it is not realisable. It is simple when both pieces are
simple, and it is a half-set profile (p = n/2) when sum b1 + sum b2 = n1 + n2 - 1. If it is also
cut-feasible, it is a counterexample to EMM.

Usage: python3 tools/emm_glue_search.py CORE_G6 CORE_PROFILE CORE_LEAF GADGETS.g6
       e.g. GsOeBW 0,0,1,1,2,0,0,0 3 data/conn5.g6
"""
import sys
from itertools import combinations

import networkx as nx

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import realis  # noqa: E402
from gemm_test import prepare, feasible  # noqa: E402

core = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(sys.argv[1].encode()))
b1 = list(map(int, sys.argv[2].split(",")))
c = int(sys.argv[3])
n1 = core.number_of_nodes()
assert core.degree(c) == 1 and b1[c] == 1
found = tested = 0
for H in nx.read_graph6(sys.argv[4]):
    H = nx.convert_node_labels_to_integers(H)
    n2 = H.number_of_nodes()
    if (n1 + n2 - 1) % 2:
        continue
    need = n1 + n2 - 1 - sum(b1)          # sum of b2 required for a half-set profile
    d2 = dict(H.degree())
    Ev2 = [v for v in H if d2[v] % 2 == 0]
    for cp in [v for v in H if d2[v] == 1]:
        for k in range(len(Ev2) + 1):
            for M in combinations(Ev2, k):
                b2 = [1 if d2[v] % 2 else (2 if v in M else 0) for v in sorted(H)]
                if sum(b2) != need or not realis.profile_ok(H, {v: b2[v] for v in H}):
                    continue
                # glue: core vertices 0..n1-1, gadget vertex v -> n1 + v, then merge cp into c
                G = core.copy()
                m = {v: (c if v == cp else n1 + v) for v in H}
                G.add_edges_from((m[a], m[z]) for a, z in H.edges())
                bb = {}
                for v in range(n1):
                    bb[v] = b1[v]
                for v in H:
                    if v != cp:
                        bb[m[v]] = b2[v]
                bb[c] = 2
                nodes = sorted(G)
                bl = [bb[v] for v in nodes]
                tested += 1
                if feasible(prepare(G), bl)[0]:
                    real = realis.profile_ok(G, {v: bb[v] for v in G})
                    found += 1
                    print("CUT-FEASIBLE glued", nx.to_graph6_bytes(G, header=False).decode().strip(),
                          "n", G.number_of_nodes(), "b", bl, "realisable", real,
                          "gadget", nx.to_graph6_bytes(H, header=False).decode().strip(), "c'", cp,
                          "M2", M, flush=True)
print(dict(tested=tested, cut_feasible=found))

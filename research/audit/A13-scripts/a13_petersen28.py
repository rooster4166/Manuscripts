#!/usr/bin/env python3
"""Audit A13: is the non-realisable cut-feasible half-set S = L of the n = 28 example
(synthesis §12, scripts/petersen_counterexample.py) a transversal of a pairing produced by Thm 21?
L is a transversal of P iff every pair of P has one vertex in L and one in R. We run the
construction (both F^v-pairing procedures) on many random spanning trees and count."""
import os
import random
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a13_check as C  # noqa: E402

P = nx.convert_node_labels_to_integers(nx.line_graph(nx.petersen_graph()))
w = 0
us = sorted(P[w])
G = nx.Graph()
G.add_edges_from((a, b) for a, b in P.edges() if w not in (a, b))
L = [f"l{i}" for i in range(1, 15)]
nx.add_path(G, ["l1"] + [f"l{i}" for i in range(5, 15)] + ["l2"])
G.add_edge("l3", "l4")
for i, u in enumerate(us, 1):
    G.add_edge(f"l{i}", u)
assert G.number_of_nodes() == 28 and all(d % 2 == 0 for _, d in G.degree())
H = nx.convert_node_labels_to_integers(G, label_attribute="name")
Lset = {v for v in H if H.nodes[v]["name"] in L}
rng = random.Random(28)
runs = transversal = 0
min_LL = None
for t in range(int(sys.argv[1]) if len(sys.argv) > 1 else 200):
    for meth in ("proof", "greedy"):
        pairs, routes, J, st = C.construct(H, rng, meth)
        runs += 1
        LR = sum(1 for a, c in pairs if (a in Lset) != (c in Lset))
        if LR == len(pairs):
            transversal += 1
        LL = sum(1 for a, c in pairs if a in Lset and c in Lset)
        min_LL = LL if min_LL is None else min(min_LL, LL)
print("n = 28 example: constructions", runs, "| L a transversal:", transversal,
      "| least number of L-L pairs:", min_LL)

"""Cores for an EMM_3 counterexample through a bridge (missing-move Section 7).

If xa is a bridge of G, every path meets the side K of x in one segment, and the edge xa lies on
one segment ending at a. So a partition of G with profile b restricts to a partition of K + xa
with profile b on K and one end at a, which is then a leaf. If that core profile is not
realisable, neither is b, whatever lies beyond the bridge.

More generally, for an edge cut delta(K) of size s, a path meets K in segments whose ends at the
boundary are the cut edges, so K plus one pendant leaf per cut edge (one end at each) must be
realisable (the temporary leaves of separating-pairs Section 11).

This script lists cores: graphs with at least one leaf (exactly one with option "one"), every
other vertex of degree >= 3, and a simple profile (1 on odd vertices, 0 or 2 on even ones) that
is cut-feasible but not realisable.
Usage: python3 tools/emm3_core_search.py [one] FILE.g6 [FILE.g6 ...]
"""
import sys
from itertools import combinations

import networkx as nx

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import realis  # noqa: E402
from gemm_test import prepare, feasible  # noqa: E402

one = "one" in sys.argv[1:]
tally = dict(graphs=0, profiles=0, feasible=0, cores=0)
for path in [a for a in sys.argv[1:] if a != "one"]:
    for G in nx.read_graph6(path):
        G = nx.convert_node_labels_to_integers(G)
        d = dict(G.degree())
        leaves = [v for v in G if d[v] == 1]
        if not leaves or (one and len(leaves) != 1) or any(d[v] < 3 for v in G if v not in leaves):
            continue
        tally["graphs"] += 1
        prep = prepare(G)
        Ev = [v for v in G if d[v] % 2 == 0]
        nodes = sorted(G)
        for k in range(len(Ev) + 1):
            for M in combinations(Ev, k):
                bb = [1 if d[v] % 2 else (2 if v in M else 0) for v in nodes]
                tally["profiles"] += 1
                if not feasible(prep, bb)[0]:
                    continue
                tally["feasible"] += 1
                if not realis.profile_ok(G, {v: bb[v] for v in G}):
                    tally["cores"] += 1
                    print("CORE", nx.to_graph6_bytes(G, header=False).decode().strip(), sorted(G.edges()),
                          "leaves", leaves, "b", bb, "p", sum(bb) // 2, flush=True)
print(tally)

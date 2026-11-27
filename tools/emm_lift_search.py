"""Search for EMM counterexamples (simple profiles of half-sets, p = n/2) built from the order-7
linkage obstruction FqJBo: add three new vertices 7, 8, 9, each joined to one or two of the
terminals {0, 2, 3}, with any edges among them. For every connected result of even order 10 and
every half-set M, compare cut-feasibility with realisability (tools/realis.c).
Usage: python3 tools/emm_lift_search.py"""
import sys
from itertools import combinations, product

import networkx as nx

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import realis  # noqa: E402
from gemm_test import prepare, feasible  # noqa: E402

core = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(b"FqJBo"))
opts = [c for r in (1, 2) for c in combinations((0, 2, 3), r)]
inner = [(7, 8), (7, 9), (8, 9)]
graphs = halfsets = feas = fails = 0
seen = set()
for att in product(opts, repeat=3):
    for mask in range(8):
        G = core.copy()
        for i, S in enumerate(att):
            for s in S:
                G.add_edge(7 + i, s)
        for j, e in enumerate(inner):
            if mask >> j & 1:
                G.add_edge(*e)
        if not nx.is_connected(G):
            continue
        key = nx.weisfeiler_lehman_graph_hash(G)
        cert = nx.to_graph6_bytes(G, header=False)
        if key in seen:
            continue
        seen.add(key)
        graphs += 1
        Ev, fam = realis.family(G)
        fam = set(fam)
        prep = prepare(G)
        nodes = sorted(G)
        for M in combinations(Ev, len(Ev) // 2):
            halfsets += 1
            bb = [1 if G.degree(v) % 2 else (2 if v in M else 0) for v in nodes]
            if feasible(prep, bb)[0]:
                feas += 1
                if frozenset(M) not in fam:
                    fails += 1
                    print("EMM FAILS", cert.decode().strip(), sorted(G.edges()), "M", M, flush=True)
print(dict(graphs=graphs, halfsets=halfsets, cut_feasible=feas, emm_failures=fails))

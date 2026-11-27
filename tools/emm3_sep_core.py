"""Cores at a vertex 2-separator, for EMM_3.

Let {s1, s2} separate G, and let H be one side with s1, s2. A partition of G restricts to H with
some numbers of ends beta_i at s_i (beta_i = d_H(s_i) mod 2, 0 <= beta_i <= d_H(s_i)): a record in
the sense of two-vertex-separators. If for a simple profile b on H - {s1, s2} no record is
realisable on H, then no G containing H in this way realises b there. Such an H is a core if some
record is cut-feasible on H, so that the cut conditions on H alone do not exclude it. We search
for cores: graphs with two terminals, every other vertex of degree >= 3.
Usage: python3 tools/emm3_sep_core.py FILE.g6 ...
"""
import sys
from itertools import combinations, product

import networkx as nx

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import realis  # noqa: E402
from gemm_test import prepare, feasible  # noqa: E402

t = dict(graphs=0, terminal_pairs=0, profiles=0, cores=0)
for path in sys.argv[1:]:
    for G in nx.read_graph6(path):
        G = nx.convert_node_labels_to_integers(G)
        d = dict(G.degree()); nodes = sorted(G)
        low = [v for v in G if d[v] < 3]
        if len(low) > 2:
            continue
        t["graphs"] += 1
        prep = prepare(G)
        for s1, s2 in combinations(nodes, 2):
            if any(v not in (s1, s2) for v in low):
                continue
            t["terminal_pairs"] += 1
            inner = [v for v in nodes if v not in (s1, s2)]
            Ev = [v for v in inner if d[v] % 2 == 0]
            recs = list(product(range(d[s1] % 2, d[s1] + 1, 2), range(d[s2] % 2, d[s2] + 1, 2)))
            for k in range(len(Ev) + 1):
                for M in combinations(Ev, k):
                    t["profiles"] += 1
                    base = {v: (1 if d[v] % 2 else (2 if v in M else 0)) for v in inner}
                    anyfeas = False; anyreal = False
                    for b1, b2 in recs:
                        bb = dict(base); bb[s1] = b1; bb[s2] = b2
                        if sum(bb.values()) == 0:
                            continue
                        if feasible(prep, [bb[v] for v in nodes])[0]:
                            anyfeas = True
                            if realis.profile_ok(G, bb):
                                anyreal = True
                                break
                    if anyfeas and not anyreal:
                        t["cores"] += 1
                        print("SEP-CORE", nx.to_graph6_bytes(G, header=False).decode().strip(),
                              sorted(G.edges()), "terminals", (s1, s2), "M", M, flush=True)
print(t)

"""Check of Lemma 7.7(d) of the missing-move manuscript on small orders.
For every cut-feasible profile of every connected graph in the files, every vertex w of degree 2
with b(w) = 2, and every neighbour x of w with b(x) <= d(x) - 2, the profile b + e_x - e_w of
G - wx must again be cut-feasible.
Usage: python3 tools/emm_reduction_check.py FILE.g6 ..."""
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from gemm_test import prepare, feasible, profiles  # noqa: E402

t = Counter()
for path in sys.argv[1:]:
    for G in nx.read_graph6(path):
        G = nx.convert_node_labels_to_integers(G)
        prep = prepare(G)
        for bb in profiles(prep[1]):
            if sum(bb) == 0 or not feasible(prep, list(bb))[0]:
                continue
            for w in G:
                if G.degree(w) == 2 and bb[w] == 2:
                    for x in G[w]:
                        if bb[x] <= G.degree(x) - 2:
                            H = G.copy(); H.remove_edge(w, x)
                            b1 = list(bb); b1[x] += 1; b1[w] -= 1
                            t["feasible" if feasible(prepare(H), b1)[0] else "INFEASIBLE"] += 1
print(dict(t))

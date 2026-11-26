"""Test the level-descent property (U*) on small even-order graphs.

C_k(G): halved endpoint vectors of decompositions into exactly k paths.
(U*): for connected G of even order n, every level k' >= n/2 + 1 with
k' - 1 >= p(G), every c in C_{k'} and every EVEN-degree r with c(r) >= 1, there is u with
c - e_u in C_{k'-1} and (c - e_u)(r) >= 1.

(U*) implies the even-order rooted test, hence Gallai (descend from any
decomposition exposing r down to level n/2).
"""
import sys
import networkx as nx
from pathnum import path_number
from endpoint_matroid import endpoint_vectors, halve


def check(G, levels_above=3):
    n = G.number_of_nodes()
    p = path_number(G)
    base = max(n // 2, p)
    C = {}
    for k in range(base, base + levels_above + 1):
        C[k] = halve(G, endpoint_vectors(G, k))
    fails = []
    for k in range(max(n // 2 + 1, p + 1), base + levels_above + 1):
        lower = C.get(k - 1, set())
        for c in C[k]:
            for r in range(n):
                if c[r] < 1 or G.degree(r) % 2:
                    continue
                ok = False
                for u in range(n):
                    if c[u] < 1:
                        continue
                    c2 = list(c); c2[u] -= 1
                    if c2[r] >= 1 and tuple(c2) in lower:
                        ok = True
                        break
                if not ok:
                    fails.append((k, c, r))
    return p, fails


if __name__ == "__main__":
    path = sys.argv[1]
    lv = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    tot = bad = 0
    for line in open(path):
        G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(line.strip().encode()))
        p, fails = check(G, lv)
        tot += 1
        if fails:
            bad += 1
            if bad <= 15:
                print("FAIL", line.strip(), "p=", p, "first:", fails[:3], "count", len(fails))
    print(f"graphs {tot}, with (U*) failures {bad}")

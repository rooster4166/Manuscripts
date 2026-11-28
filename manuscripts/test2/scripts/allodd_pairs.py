"""allodd_pairs.py: the abstract base problem of the (T2) matching lift at d(z) = 4 (test2, task 3).

G has no even vertex.  Given distinct vertices c, x, a, b with c ~/~ x and a ~/~ b, is there a
Lovasz decomposition of G with  x not in Q(c)  and  (b not in Q(a) or a not in Q(b))?
Each condition alone always holds (L1, lovasz_avoid_nonadj).  Exact search with route_ext (C).
Every connected all-odd graph on the input, every choice.  Prints the failures and a summary.
usage: python3 allodd_pairs.py ORACLE < graph6
"""
import itertools
import sys
from collections import Counter

import networkx as nx

from tb2 import Oracle


def cq(G, n, masks):
    E = list(G.edges())
    return f"C {n} {len(E)} " + " ".join(f"{u} {v}" for u, v in E) + " " + \
        " ".join("1" for _ in range(n)) + " " + " ".join(map(str, masks))


def main():
    oracle = Oracle(sys.argv[1])
    stats = Counter()
    for line in sys.stdin:
        g6 = line.strip()
        if not g6:
            continue
        G = nx.from_graph6_bytes(g6.encode())
        n = G.number_of_nodes()
        if any(G.degree(v) % 2 == 0 for v in G) or not nx.is_connected(G):
            continue
        stats["graphs"] += 1
        V = list(G)
        for c, x in itertools.permutations(V, 2):
            if G.has_edge(c, x):
                continue
            for a, b in itertools.combinations([v for v in V if v not in (c, x)], 2):
                if G.has_edge(a, b):
                    continue
                stats["choices"] += 1
                ok = False
                for (p, q) in ((a, b), (b, a)):
                    masks = [1 << v for v in range(n)]
                    masks[c] |= 1 << x
                    masks[p] |= 1 << q
                    o = oracle.query(cq(G, n, masks))
                    assert o[0] in "01"
                    if o[0] == "1":
                        ok = True
                        break
                if not ok:
                    stats["failures"] += 1
                    print("FAIL", g6, "c", c, "x", x, "pair", a, b, flush=True)
    print("SUMMARY", dict(stats))


if __name__ == "__main__":
    main()

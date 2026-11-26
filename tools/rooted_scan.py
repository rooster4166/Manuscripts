"""Scan connected graphs of even order n for the rooted (private-leaf) test.

For B of order n = 2k the rooted test asks p(B + leaf at r) <= k for every r,
which is equivalent to Gallai's conjecture over all orders.  It is only
nontrivial when p(B) = k and r has even degree (root-endpoint-costs, Sec. 1).
For those graphs we compute the full set of optimal endpoint vectors and
record, on the even vertices U, the family of exposed sets.

Usage: python3 rooted_scan.py ../data/conn8.g6 [--mconvex]
"""

from __future__ import annotations

import sys
from collections import Counter

import networkx as nx

from endpoint_matroid import endpoint_vectors, halve, m_convex_violation
from pathnum import lower_bound, path_number


def main(path: str, check_mconvex: bool):
    lines = [l.strip() for l in open(path) if l.strip()]
    stats = Counter()
    loops = []
    mviol = []
    shapes = Counter()
    for line in lines:
        G = nx.from_graph6_bytes(line.encode())
        n = G.number_of_nodes()
        assert n % 2 == 0
        k = n // 2
        U = [v for v in G if G.degree(v) % 2 == 0]
        if not U:
            stats["no even vertex"] += 1
            continue
        if lower_bound(G) < k:
            p = path_number(G)
        else:
            p = k if lower_bound(G) == k else path_number(G)
        if p > k:
            stats["GALLAI FAIL"] += 1
            loops.append(("gallai", line))
            continue
        if p < k:
            stats["p<k (trivial)"] += 1
            continue
        stats["critical p=k"] += 1
        vecs = endpoint_vectors(G, k)
        nodes = sorted(G.nodes())
        exposed = set()
        for vec in vecs:
            for v, b in zip(nodes, vec):
                if G.degree(v) % 2 == 0 and b > 0:
                    exposed.add(v)
        lp = [u for u in U if u not in exposed]
        if lp:
            loops.append(("loop", line, lp))
            stats["ROOTED FAIL"] += 1
        if check_mconvex:
            C = halve(G, vecs)
            viol = m_convex_violation(C)
            if viol is not None:
                mviol.append((line, viol, len(C)))
                stats["M-convex violation"] += 1
            else:
                stats["M-convex ok"] += 1
        shapes[(len(U), len(vecs))] += 1
    for k_, v in sorted(stats.items()):
        print(f"{k_}: {v}")
    print("critical (|U|, #optimal endpoint vectors) histogram:", sorted(shapes.items())[:40])
    for x in loops[:20]:
        print("FAIL", x)
    for x in mviol[:20]:
        print("MVIOL", x)


if __name__ == "__main__":
    main(sys.argv[1], "--mconvex" in sys.argv)

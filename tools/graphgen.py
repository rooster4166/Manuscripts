"""Generate all connected graphs on n vertices (n <= 9) up to isomorphism.

Every connected graph has a non-cut vertex, so the connected graphs on n
vertices are obtained from connected graphs on n-1 vertices by adding a vertex
with a nonempty neighbourhood.  Duplicates are removed with a Weisfeiler-Lehman
hash followed by exact isomorphism tests inside each hash bucket.

Output: one graph6 string per line.  Known counts (OEIS A001349):
n = 1..9: 1, 1, 2, 6, 21, 112, 853, 11117, 261080.
"""

from __future__ import annotations

import itertools
import sys
from typing import Dict, List

import networkx as nx


def connected_graphs(n: int) -> List[nx.Graph]:
    if n == 1:
        G = nx.Graph()
        G.add_node(0)
        return [G]
    base = connected_graphs(n - 1)
    buckets: Dict[str, List[nx.Graph]] = {}
    out: List[nx.Graph] = []
    for H in base:
        old = list(H.nodes())
        for r in range(1, n):
            for nbrs in itertools.combinations(old, r):
                G = H.copy()
                G.add_node(n - 1)
                G.add_edges_from((n - 1, u) for u in nbrs)
                key = nx.weisfeiler_lehman_graph_hash(G, iterations=4) + f"|{G.number_of_edges()}"
                lst = buckets.setdefault(key, [])
                if any(nx.is_isomorphic(G, K) for K in lst):
                    continue
                lst.append(G)
                out.append(G)
    return out


if __name__ == "__main__":
    n = int(sys.argv[1])
    gs = connected_graphs(n)
    for G in gs:
        sys.stdout.write(nx.to_graph6_bytes(G, header=False).decode())
    sys.stderr.write(f"n={n}: {len(gs)} connected graphs\n")

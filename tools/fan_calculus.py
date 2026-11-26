"""Completeness test for the Fan calculus (lean/GallaiLean/TwoEven.lean, `FanCert`).

Let G have even order and no isolated vertex, and let X be a set of even vertices. A Fan
certificate for X is a sequence of moves (x, w). Each move has x in X, xw an edge, and w adjacent
to no other vertex of X. The move deletes xw and then does one of two things:
  * even step:   w is even and not in X, and X becomes X - x;
  * odd transfer: w is odd with degree >= 3, and X becomes X - x + w.
The sequence ends when |X| <= 1. Soundness (`realisable_of_fanCert`): Ev \\ X is realisable.

Completeness question. Does every connected G of even order have a set X of even vertices with
|X| >= e/2 that admits a certificate? A certificate gives a decomposition into at most n/2 paths.

Usage: python3 tools/fan_calculus.py N [N ...]   (reads data/connN.g6; even N only)
"""
import sys
from functools import lru_cache

import networkx as nx


def analyse(G):
    n = G.number_of_nodes()
    nodes = list(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    edges = [tuple(sorted((idx[a], idx[b]))) for a, b in G.edges()]
    eid = {e: k for k, e in enumerate(edges)}
    full = (1 << len(edges)) - 1

    def adj(mask, a, b):
        k = eid.get((a, b) if a < b else (b, a))
        return k is not None and (mask >> k) & 1

    def deg(mask, v):
        return sum(1 for u in range(n) if u != v and adj(mask, u, v))

    @lru_cache(maxsize=None)
    def cert(mask, X):
        if len(X) <= 1:
            return True
        for x in X:
            for w in range(n):
                if w == x or not adj(mask, x, w):
                    continue
                if any(adj(mask, w, y) for y in X if y != x):
                    continue
                k = eid[(x, w) if x < w else (w, x)]
                m2 = mask & ~(1 << k)
                dw = deg(mask, w)
                if dw % 2 == 0 and w not in X:
                    if cert(m2, X - {x}):
                        return True
                elif dw % 2 == 1 and dw >= 3:
                    if cert(m2, (X - {x}) | {w}):
                        return True
        return False

    ev = [v for v in range(n) if deg(full, v) % 2 == 0]
    e = len(ev)
    if e <= 2:
        return e, True, None  # Lemma 3 already gives |S| <= e/2
    from itertools import combinations
    for size in range(e // 2, e + 1):
        for X in combinations(ev, size):
            if cert(full, frozenset(X)):
                return e, True, X
    return e, False, None


def main():
    for N in map(int, sys.argv[1:]):
        graphs = nx.read_graph6(f"data/conn{N}.g6")
        if not isinstance(graphs, list):
            graphs = [graphs]
        stats, fails = {}, []
        for G in graphs:
            e, ok, _ = analyse(G)
            stats.setdefault(e, [0, 0])
            stats[e][0] += 1
            if not ok:
                stats[e][1] += 1
                fails.append(G)
        print(f"n={N}: graphs={len(graphs)}  by e: " +
              ", ".join(f"e={e}: {t} ({f} fail)" for e, (t, f) in sorted(stats.items())), flush=True)
        with open(f"/tmp/claude-0/-home-user-Manuscripts/a40c9215-4484-5bc3-a3e1-2bba3a808810/scratchpad/fanfail{N}.g6", "wb") as fh:
            for G in fails:
                fh.write(nx.to_graph6_bytes(G, header=False))


if __name__ == "__main__":
    main()

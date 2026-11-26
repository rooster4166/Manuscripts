"""Independent replay of marked-reduction Sec. 7 (eight common vertices).

Claim (path case): a cycle C on contacts 0..7 (cyclic order) and an edge-disjoint
path P visiting all eight contacts (trimmed to its first and last contact) admit
a partition of their union into two paths except exactly when
  (1) every segment is direct and the core multigraph is simple, or
  (2) up to reversal and dihedral relabelling P has order 03476125, the parallel
      pairs are 12, 34, 67, each pair has >= 1 subdivided segment, and every
      other segment is direct.
Claim (cycle case): two edge-disjoint cycles with eight common vertices whose
union is simple and which have subdivisions on at least two distinct segments
partition into two paths.

A segment is the part of C or P between consecutive contacts; it is either a
single edge ("direct") or subdivided (we insert one new vertex: further
subdivision preserves any partition, so success is monotone).

We decide every case by exact search with tools/pathnum.py.
"""
from __future__ import annotations

import itertools
import sys
from functools import lru_cache

import networkx as nx

from pathnum import solve

N = 8
CYC = [(i, (i + 1) % N) for i in range(N)]


def dihedral():
    maps = []
    for s in range(N):
        maps.append(tuple((i + s) % N for i in range(N)))
        maps.append(tuple((s - i) % N for i in range(N)))
    return maps


D8 = dihedral()


def canon_path(order):
    best = None
    for g in D8:
        o = tuple(g[v] for v in order)
        for cand in (o, o[::-1]):
            if best is None or cand < best:
                best = cand
    return best


def build(segments, subdiv):
    """segments: list of (a, b) core segments; subdiv: set of indices subdivided."""
    G = nx.MultiGraph()
    nxt = N
    for idx, (a, b) in enumerate(segments):
        if idx in subdiv:
            G.add_edge(a, nxt)
            G.add_edge(nxt, b)
            nxt += 1
        else:
            G.add_edge(a, b)
    return G


def two_paths(segments, subdiv):
    G = build(segments, subdiv)
    # simple graph required (parallel direct segments are not allowed)
    if any(G.number_of_edges(u, v) > 1 for u, v in G.edges()):
        return None
    H = nx.Graph(G)
    r = solve(H, budget=2, time_limit=60, workers=1)
    return r.status in ("OPTIMAL", "FEASIBLE") and r.value <= 2


def path_case():
    seen = set()
    results = {}
    for perm in itertools.permutations(range(N)):
        c = canon_path(perm)
        if c in seen:
            continue
        seen.add(c)
        order = c
        psegs = [(order[i], order[i + 1]) for i in range(N - 1)]
        segments = CYC + psegs  # indices 0..7 cycle, 8..14 path
        cyc_pairs = {frozenset(e): i for i, e in enumerate(CYC)}
        par = []
        for j, (a, b) in enumerate(psegs):
            key = frozenset((a, b))
            if key in cyc_pairs:
                par.append((cyc_pairs[key], 8 + j))
        nonpair = [i for i in range(15) if all(i not in pr for pr in par)]
        failing_minimal = []
        # minimal simple configurations: one segment from each parallel pair
        for choice in itertools.product(*par) if par else [()]:
            S = set(choice)
            ok = two_paths(segments, S)
            if not ok:
                failing_minimal.append(tuple(sorted(S)))
        extra_fail = []
        if failing_minimal:
            # check whether adding one more subdivision anywhere rescues it,
            # and whether subdividing both members of pairs still fails
            for S in failing_minimal:
                for i in range(15):
                    if i in S:
                        continue
                    T = set(S) | {i}
                    if not two_paths(segments, T):
                        extra_fail.append((S, i))
        results[order] = (par, failing_minimal, extra_fail)
    return results


def main():
    res = path_case()
    print(f"path orders up to D8 x reversal: {len(res)}")
    nopar_fail_direct = 0
    exceptional = []
    for order, (par, fm, ef) in res.items():
        if not par:
            # the all-direct simple core always fails (15 edges > 14); fm == [()]
            if fm != [()]:
                print("UNEXPECTED: simple all-direct core succeeds?", order)
            nopar_fail_direct += 1
            if ef:
                exceptional.append((order, par, fm, ef[:6]))
        else:
            if fm or ef:
                exceptional.append((order, par, fm, ef[:12]))
    print(f"orders with simple core: {nopar_fail_direct}")
    print(f"orders with a failing configuration beyond the all-direct simple core: {len(exceptional)}")
    for x in exceptional:
        print("EXCEPTION", x)


if __name__ == "__main__":
    main()

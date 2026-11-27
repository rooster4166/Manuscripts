"""Test L_N (Lovasz decompositions avoiding a matching of forbidden pairs).

L_N: F has all degrees odd; N = {c_i a_i} is a set of pairwise disjoint pairs, each non-adjacent
in F.  Claim: F has a partition into |V|/2 paths, each vertex an end of exactly one path, such that
for every i the path ending at c_i avoids a_i, and a path with ends c_i, c_j avoids a_i and a_j.
(Equivalently, G = F + N realises the orientation c_i -> a_i with every edge c_i a_i terminal.)

Usage: python3 lovasz_matching.py [trials] [nmax]
"""
import random
import sys

import networkx as nx

import rd_lib as L


def make_all_odd(G, rng):
    ev = [v for v in G if G.degree(v) % 2 == 0]
    rng.shuffle(ev)
    while len(ev) >= 2:
        x, y = ev.pop(), ev.pop()
        if G.has_edge(x, y):
            G.remove_edge(x, y)
        else:
            G.add_edge(x, y)
    return all(G.degree(v) % 2 for v in G)


def _G(F, pairs):
    G = nx.Graph(F)
    G.add_edges_from(pairs)
    return G


def test_LN(F, pairs):
    n = F.number_of_nodes()
    routes = [[c, a] for c, a in pairs]          # R = c a, appended at c
    G = nx.Graph(F)
    G.add_edges_from(pairs)
    M = [a for c, a in pairs]
    w = L.route_respecting(G, routes, M, want=True)
    return w


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    rng = random.Random(2026)
    tot = fails = unknown = 0
    by = {}
    for it in range(trials):
        n = rng.choice([x for x in (4, 6, 8, 10, 12, 14, 16) if x <= nmax])
        F = nx.gnp_random_graph(n, rng.uniform(0.15, 0.8), seed=rng.randrange(10 ** 9))
        if not make_all_odd(F, rng) or F.number_of_edges() + n // 2 > 120:
            continue
        nonadj = [(u, v) for u in F for v in F if u < v and not F.has_edge(u, v)]
        rng.shuffle(nonadj)
        used, pairs = set(), []
        k = rng.randint(1, n // 2)
        for u, v in nonadj:
            if u in used or v in used:
                continue
            if rng.random() < 0.5:
                u, v = v, u
            pairs.append((u, v))
            used |= {u, v}
            if len(pairs) == k:
                break
        if not pairs:
            continue
        w = test_LN(F, pairs)
        if w is None and L.BUDGET is not None:
            if L.route_respecting(nx.Graph(F).copy() if False else _G(F, pairs), [[c, a] for c, a in pairs], [a for c, a in pairs]) is None:
                unknown += 1
                continue
        tot += 1
        key = (n, len(pairs))
        by.setdefault(key, [0, 0])
        by[key][0] += 1
        if w is None:
            fails += 1
            by[key][1] += 1
            print("FAIL", sorted(F.edges()), pairs, flush=True)
    print(f"L_N: {tot} instances, {fails} failures, {unknown} unknown (budget)")
    print({k: v for k, v in sorted(by.items())})


if __name__ == "__main__":
    if len(sys.argv) > 3:
        L.BUDGET = int(sys.argv[3])
        L.FINAL = False
    main()

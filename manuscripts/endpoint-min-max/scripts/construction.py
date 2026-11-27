"""Explicit good pairing (Theorem: PS holds for every connected graph of even order).

Construction:
  1. Let J be a forest T-join for T = Ev, e.g. the T-join of a spanning tree.  F = G - J has all
     degrees odd.
  2. For each vertex v, let F^v = (F - v) + {vw : w not adjacent to v}.  Its odd vertices are exactly
     the J-neighbours of v, together with v itself when v is even.  Pair them by edge-disjoint paths
     of F^v (T-join pairing lemma).
  3. Use these pairs as the transitions of J at v (the partner of v gives the end edge at v).  Since
     J is a forest, the transitions decompose J into paths pairing Ev.  This pairing is good.

The script checks the claim against the cut enumeration (tools/cutfeas.c) for several random spanning
trees per graph.

Usage: python3 construction.py [6] [8] [10] [bottleneck] [trees] [random12]
"""
import collections
import random
import sys
import time

import networkx as nx

import emm_lib as L
from certificates import good


def tjoin_pairing(H):
    """Pair the odd-degree vertices of the (simple) graph H by edge-disjoint paths (Lemma 14)."""
    H = nx.Graph(H)
    pairs = []
    while H.number_of_edges():
        try:
            cyc = nx.find_cycle(H)
            H.remove_edges_from(cyc)
            continue
        except nx.NetworkXNoCycle:
            pass
        comp = next(c for c in nx.connected_components(H) if len(c) > 1)
        leaves = [x for x in comp if H.degree(x) == 1]
        a, c = leaves[0], leaves[1]
        p = nx.shortest_path(H, a, c)
        H.remove_edges_from(zip(p, p[1:]))
        pairs.append((a, c))
    return pairs


def tree_tjoin(S, T):
    """The unique T-join of the tree S."""
    T = set(T)
    J = set()
    root = next(iter(S))
    order = list(nx.dfs_preorder_nodes(S, root))
    parent = {root: None}
    for u in order:
        for w in S[u]:
            if w not in parent:
                parent[w] = u
    below = {u: (u in T) for u in S}
    for u in reversed(order):
        if parent[u] is not None:
            if below[u]:
                J.add(frozenset((u, parent[u])))
            below[parent[u]] ^= below[u]
    return J


def construct(G, J):
    """Return (pairing, routes) built from the forest T-join J by the F^v transitions."""
    n = G.number_of_nodes()
    F = nx.Graph()
    F.add_nodes_from(G)
    F.add_edges_from(e for e in G.edges() if frozenset(e) not in J)
    trans = {}          # trans[(v, x)] = y : the route entering v from x leaves to y (None = ends at v)
    for v in G:
        NJ = [x for x in G[v] if frozenset((v, x)) in J]
        if not NJ:
            continue
        Fv = F.copy()
        Fv.remove_edges_from([(v, x) for x in list(Fv[v])])
        Fv.add_edges_from((v, w) for w in G if w != v and not G.has_edge(v, w))
        odd = {x for x in Fv if Fv.degree(x) % 2}
        assert odd == set(NJ) | ({v} if G.degree(v) % 2 == 0 else set()), "parity claim fails"
        for a, c in tjoin_pairing(Fv):
            if a == v:
                trans[(v, c)] = None
            elif c == v:
                trans[(v, a)] = None
            else:
                trans[(v, a)] = c
                trans[(v, c)] = a
    Ev = L.even_vertices(G)
    routes, used = [], set()
    for s in Ev:
        if any(s in (r[0], r[-1]) for r in routes):
            continue
        # the end edge at s: the J-neighbour x with trans[(s, x)] is None
        x = next(x for x in G[s] if frozenset((s, x)) in J and trans.get((s, x), 0) is None)
        path, prev, cur = [s], s, x
        while True:
            path.append(cur)
            nxt = trans[(cur, prev)]
            if nxt is None:
                break
            prev, cur = cur, nxt
        E = {frozenset((path[i], path[i + 1])) for i in range(len(path) - 1)}
        assert len(set(path)) == len(path) and not (E & used), "routes are not edge-disjoint paths"
        used |= E
        routes.append(path)
    assert used == J
    return [(r[0], r[-1]) for r in routes], routes


def run(name, graphs, trees_per_graph=3, seed=1):
    rng = random.Random(seed)
    t = time.time()
    bad = 0
    checked = 0
    for G, F in zip(graphs, L.cut_feasible(graphs)):
        Ev = L.even_vertices(G)
        for i in range(trees_per_graph):
            H = G.copy()
            for u, w in H.edges():
                H[u][w]["weight"] = rng.random()
            S = nx.minimum_spanning_tree(H)
            J = tree_tjoin(S, Ev)
            P, routes = construct(G, J)
            checked += 1
            if not good(P, F):
                bad += 1
                print("   NOT GOOD:", sorted(G.edges()), P, flush=True)
    print(f"{name}: {len(graphs)} graphs, {checked} constructions, {bad} not good   [{time.time() - t:.0f}s]",
          flush=True)


def main():
    for w in sys.argv[1:] or ["6", "8", "10", "bottleneck", "trees", "random12"]:
        if w in ("6", "8"):
            run(f"all connected, order {w}", L.all_connected(int(w)))
        elif w == "10":
            run("random G(10,p), seed 20261127", L.random_sample())
        elif w == "bottleneck":
            run("bottleneck families", L.bottleneck())
        elif w == "trees":
            for n in (8, 10, 12):
                run(f"trees, order {n}", [T for T in (L.relabel(T) for T in nx.nonisomorphic_trees(n))
                                         if len(L.even_vertices(T)) >= 2], trees_per_graph=1)
        elif w == "random12":
            run("random G(12,p), seed 12", L.random_sample(n=12, count=150, seed=12), trees_per_graph=2)


if __name__ == "__main__":
    main()

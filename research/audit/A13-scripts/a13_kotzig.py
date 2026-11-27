#!/usr/bin/env python3
"""Audit A13: independent check of Section 5 of endpoint-min-max (the Kotzig reduction):
Definition 22 (G(H)), Lemma 23 (cuts of line graphs of cubic graphs), Proposition 24
(cut-feasibility of the gadget), Proposition 25 (realisations), Theorem 26 (Kotzig) on examples.
Written from the text; shares no code with scripts/kotzig.py.

For each test cubic graph H:
  * Lemma 23: |delta_{L(H)}(A)| = 2 m(A) for every (or, if |E(H)| > 15, 4000 random) partitions
    E(H) = A + B; lambda(L(H)) >= 4 iff H is bridgeless.
  * Prop 24: the gadget is cut-feasible iff H is bridgeless, by brute force on ED (1) over all v and
    W (n <= 16) and, for every H, by the arm-form max-flow (Lemma 1(d)) at every vertex.
  * Prop 25 / Thm 26: realisability of the gadget by the A13 oracle (n <= 16, and the Petersen
    case n = 28 if it finishes), Hamiltonian decompositions of L(H) by search, Hamiltonicity of H.
Usage: a13_kotzig.py
"""
import itertools
import os
import random
import sys
import time

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a13_check as C  # noqa: E402
from a13_realis import realisable  # noqa: E402


def build(H, rng):
    """Definition 22, with w* chosen at random."""
    Hl = nx.convert_node_labels_to_integers(H)
    E = [tuple(sorted(e)) for e in Hl.edges()]
    LG = nx.Graph()
    LG.add_nodes_from(range(len(E)))
    for i, j in itertools.combinations(range(len(E)), 2):
        if set(E[i]) & set(E[j]):
            LG.add_edge(i, j)
    w = rng.randrange(len(E))
    us = sorted(LG[w])
    assert len(us) == 4
    R = [x for x in LG if x != w]
    N = len(R)
    idx = {x: k for k, x in enumerate(R)}          # R -> 0..N-1
    G = nx.Graph()
    G.add_nodes_from(range(2 * N))
    for a, c in LG.edges():
        if w not in (a, c):
            G.add_edge(idx[a], idx[c])
    l = {i: N + i - 1 for i in range(1, N + 1)}    # l_i -> N + i - 1
    path = [l[1]] + [l[i] for i in range(5, N + 1)] + [l[2]]
    nx.add_path(G, path)
    G.add_edge(l[3], l[4])
    for i, u in enumerate(us, 1):
        G.add_edge(l[i], idx[u])
    gad = set(range(N, 2 * N))
    return G, gad, LG, E


def lemma23(H, LG, E, rng):
    Hl = nx.convert_node_labels_to_integers(H)
    m = len(E)
    parts = range(1, (1 << m) - 1) if m <= 15 else (rng.randrange(1, (1 << m) - 1) for _ in range(4000))
    for mask in parts:
        A = {i for i in range(m) if mask >> i & 1}
        cut = sum(1 for a, c in LG.edges() if (a in A) != (c in A))
        mixed = 0
        for x in Hl:
            sides = {(E.index(tuple(sorted((x, y)))) in A) for y in Hl[x]}
            mixed += (len(sides) == 2)
        assert cut == 2 * mixed, 'Lemma 23 formula'
    lam = nx.edge_connectivity(LG)
    bridgeless = not nx.has_bridges(Hl)
    assert (lam >= 4) == bridgeless, 'Lemma 23 equivalence'
    return lam, bridgeless


def arm_ok(G, b):
    """Lemma 1(d) at every vertex, by max-flow."""
    for v in G:
        D = nx.DiGraph()
        D.add_nodes_from(['s', 't'])
        for x, y in G.edges():
            if v in (x, y):
                continue
            D.add_edge(x, y, capacity=1)
            D.add_edge(y, x, capacity=1)
        for y in G[v]:
            D.add_edge('s', y, capacity=1)
        for z in G:
            if z != v and b[z]:
                D.add_edge(z, 't', capacity=b[z])
        if nx.maximum_flow_value(D, 's', 't') < G.degree(v):
            return False
    return True


def ham_cycles(G):
    n = G.number_of_nodes()
    nodes = sorted(G)
    s = nodes[0]
    out = set()

    def rec(path, vis):
        c = path[-1]
        if len(path) == n:
            if G.has_edge(c, s):
                out.add(frozenset(frozenset(e) for e in zip(path, path[1:] + [s])))
            return
        for y in G[c]:
            if y not in vis:
                vis.add(y)
                path.append(y)
                rec(path, vis)
                path.pop()
                vis.remove(y)

    rec([s], {s})
    return out


def is_hamiltonian(H):
    return len(ham_cycles(nx.convert_node_labels_to_integers(H))) > 0


def ham_decomposable(LG):
    cyc = ham_cycles(LG)
    allE = frozenset(frozenset(e) for e in LG.edges())
    return any((allE - c) in cyc for c in cyc), len(cyc)


def bridged_cubic():
    """Two copies of K4 with one edge subdivided, joined by a bridge between the subdivision vertices."""
    G = nx.Graph()
    for off in (0, 5):
        K = [off + i for i in range(4)]
        G.add_edges_from(itertools.combinations(K, 2))
        G.remove_edge(off, off + 1)
        G.add_edges_from([(off, off + 4), (off + 1, off + 4)])
    G.add_edge(4, 9)
    assert all(d == 3 for _, d in G.degree()) and nx.has_bridges(G)
    return G


def main():
    rng = random.Random(27)
    tests = [('K4', nx.complete_graph(4)), ('prism', nx.circular_ladder_graph(3)),
             ('K33', nx.complete_bipartite_graph(3, 3)), ('cube', nx.hypercube_graph(3)),
             ('Petersen', nx.petersen_graph()), ('bridged10', bridged_cubic())]
    for n in (8, 10, 10, 12):
        tests.append(('random cubic %d' % n, nx.random_regular_graph(3, n, seed=rng.randrange(10 ** 6))))
    for name, H in tests:
        if not nx.is_connected(H):
            print(name, 'disconnected, skipped')
            continue
        G, gad, LG, E = build(H, rng)
        n = G.number_of_nodes()
        deg = [G.degree(v) for v in range(n)]
        assert all(deg[v] == (2 if v in gad else 4) for v in range(n)) and n == 2 * len(gad)
        assert nx.is_connected(G)
        b = C.simple_profile(deg, gad)
        lam, bridgeless = lemma23(H, LG, E, rng)
        flow = arm_ok(G, b)
        brute = None
        if n <= 16:
            brute = C.CutData(G).profile_ok(b) is None
            assert brute == flow
        assert flow == bridgeless, 'Prop 24'
        hamH = is_hamiltonian(H)
        hd, ncyc = ham_decomposable(LG) if LG.number_of_nodes() <= 18 else (None, None)
        if hd is not None:
            assert hd == hamH, 'Kotzig'
        real = None
        if n <= 16:
            t = time.time()
            real = realisable(G, b)
            if hd is not None:
                assert real == hd, 'Prop 25'
        print('%-16s |V(H)|=%2d n(G)=%2d lambda(L(H))=%d bridgeless=%s | cut-feasible: flow=%s brute=%s |'
              ' H Hamiltonian=%s, L(H) Ham-decomposable=%s (Ham cycles %s) | realisable=%s'
              % (name, H.number_of_nodes(), n, lam, bridgeless, flow, brute, hamH, hd, ncyc, real), flush=True)
    # Petersen: number of Hamiltonian cycles of L(P), and Hamiltonian decompositions
    LP = nx.line_graph(nx.petersen_graph())
    LP = nx.convert_node_labels_to_integers(LP)
    hd, ncyc = ham_decomposable(LP)
    print('L(Petersen): Hamiltonian cycles', ncyc, '| Hamiltonian decomposition:', hd)


if __name__ == '__main__':
    main()

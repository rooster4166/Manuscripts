#!/usr/bin/env python3
"""Audit A13: independent check of the second proof of Theorem 21 (research/connections.md §U,
author commit b7923d3): the cut-form pairing lemma applied to one auxiliary graph B on V x V.
Written from the description in connections §U; shares no code with scripts/auxgraph.py.

  (1) Pairing lemma: for any graph Gam, Odd(Gam) has a pairing pi with sigma_pi(S) <= |delta(S)|
      for all S. Implemented by the edge-deletion recursion (edges inserted in random order), and
      tested by brute force over all S on random graphs of order <= 12.
  (2) B: copy v carries F^v on {v} x V; each J-edge vx gives (v,x)-(x,v). Checked: Odd(B) =
      {(v,v): v in Ev}; for every v and Y not containing v, with S = {(u,w): u in Y} u {(v,w): w in Y},
      |delta_B(S)| = |delta_{G^v}(Y)| and sigma_pi(S) = sigma_P(Y).
  (3) The induced pairing P of Ev is good, by brute force on ED (1) for every transversal.
J is taken both as a spanning-tree T-join (a forest) and as that T-join plus random cycles of
G (symmetric difference), which is NOT a forest: the second proof does not need forests.
Usage: a13_auxgraph.py FILE [trials]   |   a13_auxgraph.py lemma
"""
import itertools
import os
import random
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a13_check as C  # noqa: E402


def pair_by_deletion(Gam, rng):
    """Edge-deletion proof, run forwards: add the edges one by one and update the pairing."""
    E = list(Gam.edges())
    rng.shuffle(E)
    pi = {}
    for x, y in E:
        # before adding xy: pi pairs the odd vertices of the current graph H' = H - xy
        ox, oy = x in pi, y in pi
        if ox and oy:
            a, b = pi.pop(x), pi.pop(y)
            if a == y:
                pass                                  # {x, y} was a pair: drop it
            else:
                pi.pop(a)
                pi.pop(b)
                pi[a], pi[b] = b, a                   # {x, a}, {y, b} -> {a, b}
        elif ox:                                      # x odd, y even in H': x even, y odd in H
            a = pi.pop(x)
            pi.pop(a)
            pi[y], pi[a] = a, y
        elif oy:
            b = pi.pop(y)
            pi.pop(b)
            pi[x], pi[b] = b, x
        else:
            pi[x], pi[y] = y, x
    odd = {u for u in Gam if Gam.degree(u) % 2}
    assert set(pi) == odd and all(pi[pi[u]] == u and pi[u] != u for u in pi)
    return {frozenset((u, pi[u])) for u in pi}


def lemma_test(count=300, seed=5):
    rng = random.Random(seed)
    for t in range(count):
        n = rng.randint(2, 12)
        Gam = nx.gnp_random_graph(n, rng.choice([.2, .35, .5, .7]), seed=rng.randrange(10 ** 9))
        pairs = pair_by_deletion(Gam, rng)
        for mask in range(1 << n):
            S = {v for v in range(n) if mask >> v & 1}
            cut = sum(1 for a, c in Gam.edges() if (a in S) != (c in S))
            sig = sum(1 for p in pairs if len(p & S) == 1)
            assert sig <= cut, ('pairing lemma fails', t)
    print('pairing lemma (edge deletion): %d random graphs of order 2..12, all S: no violation' % count)


def build_B(G, J):
    n = G.number_of_nodes()
    adj = [set(G[v]) for v in range(n)]
    F = [(a, c) for a, c in G.edges() if C.edge(a, c) not in J]
    B = nx.Graph()
    B.add_nodes_from((v, w) for v in range(n) for w in range(n))
    for v in range(n):
        for a, c in F:
            if v not in (a, c):
                B.add_edge((v, a), (v, c))
        for w in range(n):
            if w != v and w not in adj[v]:
                B.add_edge((v, v), (v, w))
    for a, c in J:
        B.add_edge((a, c), (c, a))
    return B


def random_tjoin(G, rng, forest):
    n = G.number_of_nodes()
    Ev = {v for v in range(n) if G.degree(v) % 2 == 0}
    J = C.tree_tjoin(C.random_spanning_tree(G, rng), Ev)
    if not forest:
        for _ in range(3):                           # add random cycles (symmetric difference)
            try:
                H = G.copy()
                for a, c in H.edges():
                    H[a][c]['w'] = rng.random()
                cyc = nx.find_cycle(H, source=rng.randrange(n))
            except nx.NetworkXNoCycle:
                break
            J ^= {C.edge(a, c) for a, c in cyc}
    return J, Ev


def check(G, rng, forest, deep):
    G = nx.convert_node_labels_to_integers(G)
    n = G.number_of_nodes()
    J, Ev = random_tjoin(G, rng, forest)
    Jg = nx.Graph()
    Jg.add_nodes_from(range(n))
    Jg.add_edges_from(J)
    assert {v for v in range(n) if Jg.degree(v) % 2} == Ev
    B = build_B(G, J)
    oddB = {x for x in B if B.degree(x) % 2}
    assert oddB == {(v, v) for v in Ev}, 'Odd(B)'
    pairsB = pair_by_deletion(B, rng)
    P = [tuple(sorted(x[0] for x in p)) for p in pairsB]
    if deep:
        adj = [set(G[v]) for v in range(n)]
        for v in range(n):
            others = [w for w in range(n) if w != v]
            for r in range(len(others) + 1):
                for Y in itertools.combinations(others, r):
                    Ys = set(Y)
                    S = {(u, w) for u in Ys for w in range(n)} | {(v, w) for w in Ys}
                    dB = sum(1 for x, y in B.edges() if (x in S) != (y in S))
                    out = set(range(n)) - Ys - {v}
                    dGv = sum(1 for y in Ys for w in adj[y] if w in out) + sum(1 for y in Ys if y not in adj[v])
                    assert dB == dGv, 'cut identity'
                    sB = sum(1 for p in pairsB if len(p & S) == 1)
                    sP = sum(1 for a, c in P if (a in Ys) != (c in Ys))
                    assert sB == sP <= dGv
    fail = C.pairing_good_bruteforce(C.CutData(G), P)
    return fail, nx.is_forest(Jg)


def run(path, trials):
    rng = random.Random(21)
    graphs = cons = nonforest = 0
    for line in open(path):
        G = nx.from_graph6_bytes(line.strip().encode())
        if G.number_of_nodes() % 2:
            continue
        graphs += 1
        deep = G.number_of_nodes() <= 6 or graphs % 50 == 0
        for t in range(trials):
            for forest in (True, False):
                fail, isf = check(G, rng, forest, deep)
                cons += 1
                nonforest += (not isf)
                if fail is not None:
                    print('FAILURE', line.strip(), fail, flush=True)
                    return
    print(path, 'graphs', graphs, 'constructions', cons, '(non-forest J in %d)' % nonforest,
          '| Odd(B), cut identity (deep sample), goodness by brute force: no failure')


if __name__ == '__main__':
    if sys.argv[1] == 'lemma':
        lemma_test()
    else:
        run(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 1)

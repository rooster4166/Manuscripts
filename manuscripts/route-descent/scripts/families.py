"""Test families for route descent (all relabelled to 0..n-1).

  order12()   the 12 order-12 EMM counterexamples (missing-move Thm 7.5; research/experiments.md E17/E18)
  g18()       G_18 = D_2 + K_{4,4} + {sp, sb0} (endpoint-min-max Thm 41)
  g2(half)    G_2, half (n = 20) or full (n = 32) blow-up (endpoint-min-max Thm 42)
  gbad()      the order-28 Petersen counterexample G_bad (synthesis section 12)
  random_graphs(n, count, seed)  connected G(n, p), p uniform in [.25, .7]
"""
import os
import random
import sys
from itertools import combinations

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", "..", ".."))
EMM = os.path.join(ROOT, "manuscripts", "endpoint-min-max", "scripts")


def relabel(G):
    return nx.convert_node_labels_to_integers(G, ordering="sorted" if all(isinstance(v, int) for v in G) else "default")


def order12():
    path = os.path.join(ROOT, "manuscripts", "missing-move", "scripts", "outputs", "emm_counterexamples12.g6")
    out = []
    for line in open(path):
        s = line.strip()
        if s:
            out.append((s, relabel(nx.from_graph6_bytes(s.encode()))))
    return out


def g18():
    a0, a1, a2, a3, b0, b1, b2, b3, p, q = range(10)
    D = nx.Graph()
    D.add_edges_from(combinations([a0, a1, a2, a3], 2))
    D.add_edges_from(combinations([b0, b1, b2, b3], 2))
    D.add_edges_from([(p, a1), (p, a2), (p, b1), (q, a3), (q, b2), (q, b3)])
    G = D.copy()
    S = list(range(10, 18))
    G.add_edges_from((x, y) for x in S[:4] for y in S[4:])
    G.add_edges_from([(10, p), (10, b0)])
    return relabel(G), set(range(10))          # vertex set of the gadget


def g2(half=True):
    sys.path.insert(0, EMM)
    import emm_connectivity as C
    r, k = 2, 4
    blown = set(range(1, k, 2)) if half else set(range(k))
    D, port = C.build(r, blown)
    G, S = C.host(r, D, port)
    G = C.fix_parity(G, S)
    H = nx.convert_node_labels_to_integers(G, label_attribute="old")
    gadget = {v for v in H if H.nodes[v]["old"] not in set(S)}
    H2 = nx.Graph()
    H2.add_nodes_from(H)
    H2.add_edges_from(H.edges())
    return H2, gadget


def gbad():
    P = nx.petersen_graph()
    LG = nx.convert_node_labels_to_integers(nx.line_graph(P))
    w = 0
    us = sorted(LG[w])
    G = nx.Graph()
    G.add_edges_from((a, b) for a, b in LG.edges() if w not in (a, b))
    path = ["l1"] + [f"l{i}" for i in range(5, 15)] + ["l2"]
    nx.add_path(G, path)
    G.add_edge("l3", "l4")
    for i, u in enumerate(us, 1):
        G.add_edge(f"l{i}", u)
    H = nx.convert_node_labels_to_integers(G, label_attribute="old")
    R = {v for v in H if not str(H.nodes[v]["old"]).startswith("l")}
    H2 = nx.Graph()
    H2.add_nodes_from(H)
    H2.add_edges_from(H.edges())
    return H2, R


def random_graphs(n, count, seed, pmin=0.25, pmax=0.7, mmax=64, min_even=2):
    rng = random.Random(seed)
    out = []
    while len(out) < count:
        G = nx.gnp_random_graph(n, rng.uniform(pmin, pmax), seed=rng.randrange(10 ** 9))
        if not nx.is_connected(G) or G.number_of_edges() > mmax:
            continue
        if sum(1 for v in G if G.degree(v) % 2 == 0) < min_even:
            continue
        out.append(G)
    return out


def kotzig_even(name):
    """G'(H) of endpoint-min-max Thm 45 (all degrees even, >= 4): H = prism (n = 16) or
    petersen (n = 28)."""
    sys.path.insert(0, EMM)
    import kotzig_even as KE
    H = nx.circular_ladder_graph(3) if name == "prism" else nx.petersen_graph()
    G = KE.build(H)[0]
    H2 = nx.convert_node_labels_to_integers(G, label_attribute="old")
    out = nx.Graph()
    out.add_nodes_from(H2)
    out.add_edges_from(H2.edges())
    return out


def block_graphs(count, seed, nmax=20):
    """Random 'block trees': small dense blocks (K4, K5, K5 - e, C5, K33) joined along a random tree
    by paths of length 1-3, plus a few random chords; even order only."""
    rng = random.Random(seed)
    blocks = [nx.complete_graph(4), nx.complete_graph(5), nx.complete_graph(5), nx.cycle_graph(5),
              nx.complete_bipartite_graph(3, 3)]
    blocks[2].remove_edge(0, 1)
    out = []
    while len(out) < count:
        k = rng.randint(2, 4)
        G = nx.Graph()
        reps = []
        for i in range(k):
            B = nx.convert_node_labels_to_integers(rng.choice(blocks), first_label=G.number_of_nodes())
            G = nx.union(G, B)
            reps.append(list(B.nodes()))
        for i in range(1, k):
            j = rng.randrange(i)
            u, w = rng.choice(reps[i]), rng.choice(reps[j])
            L = rng.randint(1, 3)
            prev = u
            for _ in range(L - 1):
                x = G.number_of_nodes()
                G.add_edge(prev, x)
                prev = x
            G.add_edge(prev, w)
        for _ in range(rng.randint(0, 2)):
            a, b = rng.sample(list(G.nodes()), 2)
            G.add_edge(a, b)
        G = nx.convert_node_labels_to_integers(G)
        if G.number_of_nodes() % 2 or G.number_of_nodes() > nmax or G.number_of_edges() > 100:
            continue
        if sum(1 for v in G if G.degree(v) % 2 == 0) < 2:
            continue
        out.append(G)
    return out

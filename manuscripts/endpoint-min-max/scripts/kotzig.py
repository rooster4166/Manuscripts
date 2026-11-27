"""The Kotzig reduction (project lead's construction; manuscript Theorem on NP-hardness).

For a connected cubic graph H, G(H) is built as follows:
  - R = L(H) - w*, where w* is a vertex of the line graph L(H) with neighbours u1..u4;
  - a gadget L = {l1..lN}, N = |R|: the path l1 l5 l6 ... lN l2, the edge l3 l4, and the cross edges
    li ui (i = 1..4).
All degrees are even (4 on R, 2 on L), n = 2N, and L is a half-set.  The manuscript proves:
  (i)  L is cut-feasible iff L(H) is 4-edge-connected iff H is bridgeless;
  (ii) L is realisable iff L(H) has a Hamiltonian decomposition iff (Kotzig) H is Hamiltonian.
This script checks (i) with the max-flow arm test (Lemma 1(d)), cross-checked by brute force where
small, and (ii) with the exact oracle (n <= 16) and a direct search for Hamiltonian decompositions.

Usage: python3 kotzig.py
"""
import itertools
import random

import networkx as nx

import emm_lib as L


def build(H, wstar=None):
    LG = nx.convert_node_labels_to_integers(nx.line_graph(H))
    w = 0 if wstar is None else wstar
    us = sorted(LG[w])
    R = [v for v in LG if v != w]
    N = len(R)
    G = nx.Graph()
    G.add_edges_from((a, b) for a, b in LG.edges() if w not in (a, b))
    lab = {i: N + i for i in range(1, N + 1)}              # l_i -> vertex N + i (R is 1..N)
    nx.add_path(G, [lab[1]] + [lab[i] for i in range(5, N + 1)] + [lab[2]])
    G.add_edge(lab[3], lab[4])
    for i, u in enumerate(us, 1):
        G.add_edge(lab[i], u)
    G = nx.convert_node_labels_to_integers(G, ordering="sorted")
    Lset = set(range(N, 2 * N))
    return G, Lset, LG


def arm_ok(G, b, v):
    """Lemma 1(d): the d(v) edges at v extend to edge-disjoint arms in G - v ending at b."""
    D = nx.DiGraph()
    s, t = "s", "t"
    for a, c in G.edges():
        if v in (a, c):
            continue
        D.add_edge(a, c, capacity=1)
        D.add_edge(c, a, capacity=1)
    for y in G[v]:
        D.add_edge(s, y, capacity=1)
    for z in G:
        if z != v and b[z] > 0:
            D.add_edge(z, t, capacity=b[z])
    if t not in D or s not in D:
        return G.degree(v) == 0
    return nx.maximum_flow_value(D, s, t) == G.degree(v)


def cut_feasible_flow(G, M):
    b = {v: G.degree(v) % 2 + (2 if v in M else 0) for v in G}
    return all(arm_ok(G, b, v) for v in G)


def ham_decomposable(LG):
    n = LG.number_of_nodes()
    allE = frozenset(frozenset(e) for e in LG.edges())
    cycles = set()

    def dfs(path, used):
        u = path[-1]
        if len(path) == n:
            if LG.has_edge(u, path[0]):
                cycles.add(frozenset(frozenset((path[i], path[(i + 1) % n])) for i in range(n)))
            return
        for w in LG[u]:
            if w not in used:
                used.add(w)
                path.append(w)
                dfs(path, used)
                path.pop()
                used.discard(w)

    dfs([0], {0})
    return any((allE - c) in cycles for c in cycles)


def hamiltonian(H):
    n = H.number_of_nodes()
    s = next(iter(H))

    def dfs(path, used):
        if len(path) == n:
            return H.has_edge(path[-1], s)
        return any(dfs(path + [w], used | {w}) for w in H[path[-1]] if w not in used)

    return dfs([s], {s})


def main():
    rng = random.Random(5)
    tests = [("K4", nx.complete_graph(4)), ("prism", nx.circular_ladder_graph(3)),
             ("K33", nx.complete_bipartite_graph(3, 3)), ("cube", nx.hypercube_graph(3)),
             ("Petersen", nx.petersen_graph())]
    # a cubic graph with a bridge: two copies of K4 with one edge subdivided, the two subdivision
    # vertices joined by an edge
    B = nx.Graph()
    for off in (0, 5):
        B.add_edges_from([(off + a, off + c) for a, c in [(0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 4), (4, 1)]])
    B.add_edge(4, 9)
    tests.append(("bridged", B))
    for i in range(6):
        tests.append((f"random cubic {2 * (4 + i)}", nx.random_regular_graph(3, 2 * (4 + i), seed=rng.randrange(10**6))))
    for name, H in tests:
        if not nx.is_connected(H) or any(d != 3 for _, d in H.degree()):
            print(name, "skipped (not connected cubic)")
            continue
        H = nx.convert_node_labels_to_integers(H)
        bridgeless = not any(True for _ in nx.bridges(H))
        G, Lset, LG = build(H)
        assert all(d % 2 == 0 for _, d in G.degree()) and nx.is_connected(G)
        cf = cut_feasible_flow(G, Lset)
        lam4 = nx.edge_connectivity(LG) >= 4
        line = (f"{name:18s} n={G.number_of_nodes():3d} bridgeless={bridgeless!s:5s} "
                f"lambda(L(H))>=4={lam4!s:5s} L cut-feasible={cf!s:5s}")
        assert cf == lam4 == bridgeless, line
        if G.number_of_nodes() <= 10:
            assert (frozenset(Lset) in L.cut_feasible([G])[0]) == cf      # brute force cross-check
        ham = hamiltonian(H)
        if LG.number_of_nodes() <= 24:
            hd = ham_decomposable(LG)
            line += f" H Hamiltonian={ham!s:5s} L(H) Ham-decomposable={hd!s:5s}"
            assert hd == ham, "Kotzig's theorem fails?!"
        if G.number_of_nodes() <= 16:
            b = {v: 2 if v in Lset else 0 for v in G}
            real = L.realis.profile_ok(G, b)
            line += f" L realisable={real}"
            assert real == (ham and bridgeless) or not bridgeless
        print(line, flush=True)


if __name__ == "__main__":
    main()

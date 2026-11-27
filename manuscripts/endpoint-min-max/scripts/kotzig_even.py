"""The Kotzig reduction at even degrees >= 4 (manuscript Theorem "hardness at even degrees").

For a connected bridgeless cubic graph H with N = |E(H)| - 1 >= 6, G'(H) is built as follows:
  - R = L(H) - w*, where w* is a vertex of the line graph L(H) with neighbours u1..u4;
  - S = N new vertices, all marked, containing t1..t4, with the cross edges ui ti;
  - on S the complete graph minus {t1t2, t3t4} (N odd), or minus a perfect matching of S - T
    (N even; the matching is the end matching of a zigzag decomposition, see below).
Every degree is even and at least 4, n = 2N, and M = S is a half-set.  The manuscript proves:
  (i)   M is cut-feasible when H is bridgeless (arms through L(H), by 4-edge-connectivity);
  (ii)  M is realisable iff L(H) has a Hamiltonian decomposition iff (Kotzig) H is Hamiltonian;
  (iii) G'(H) is 4-edge-connected.
This script checks (i) by max-flow at every vertex (Lemma 1(d)), (iii) with networkx, and (ii) by
building the realisation explicitly from a Hamiltonian decomposition of L(H) and the zigzag
decompositions of the clique, by the exact oracle where n <= 16, and by the search for
Hamiltonian decompositions where L(H) has at most 24 vertices (as in kotzig.py).

Usage: python3 kotzig_even.py
"""
import os
import random
import sys

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "..", "tools")))
import realis  # noqa: E402

from kotzig import hamiltonian, cut_feasible_flow  # noqa: E402


def zigzag(m):
    """Walecki's zigzag: m Hamiltonian paths decomposing K_{2m} on 0..2m-1; P_j runs
    j, j+1, j-1, j+2, j-2, ..., j+m and has ends j, j+m."""
    k = 2 * m
    paths = []
    for j in range(m):
        P = [j]
        for s in range(1, m + 1):
            P.append((j + s) % k)
            if s < m:
                P.append((j - s) % k)
        paths.append(P)
    E = [frozenset(e) for P in paths for e in zip(P, P[1:])]
    assert len(E) == len(set(E)) == k * (k - 1) // 2
    return paths


def surplus_clique(N):
    """The graph S on 0..N-1 with T = {0, 1, 2, 3} = t1..t4, and a realisation of the profile
    1 on T, 2 elsewhere (a list of paths).  N odd: K_N - {t1t2, t3t4}; N even: K_N minus a
    perfect matching of S - T."""
    assert N >= 6
    if N % 2 == 1:
        m = (N - 1) // 2
        Z = zigzag(m)                       # on 0..2m-1; infinity = 2m
        inf = 2 * m
        cycles = [[inf] + P + [inf] for P in Z]
        # e in C_0, f in C_1 disjoint from e
        e = (cycles[0][1], cycles[0][2])
        f = next((a, b) for a, b in zip(cycles[1], cycles[1][1:]) if not {a, b} & set(e))
        # relabel: e -> (0, 1), f -> (2, 3)
        order = [e[0], e[1], f[0], f[1]] + [v for v in range(N) if v not in (e[0], e[1], f[0], f[1])]
        lab = {v: i for i, v in enumerate(order)}
        cyc = [[lab[v] for v in C] for C in cycles]
        S = nx.complete_graph(N)
        S.remove_edges_from([(0, 1), (2, 3)])
        paths = []

        def open_at(C, a, b):
            """the cycle C (closed list) minus the edge ab, as a path from a to b"""
            C = C[:-1]
            i = C.index(a)
            C = C[i:] + C[:i]                 # starts at a
            if C[1] == b:
                C = [C[0]] + C[1:][::-1]      # now a ... b with ab not used
            assert C[-1] == b
            return C

        # C_0 - t1t2: a path t1 .. t2; split at one interior vertex x not in T
        P0 = open_at(cyc[0], 0, 1)
        nonT = [v for v in range(4, N)]
        x = next(v for v in P0[1:-1] if v >= 4)
        i = P0.index(x)
        paths += [P0[: i + 1], P0[i:]]
        P1 = open_at(cyc[1], 2, 3)
        paths.append(P1)
        rest = [v for v in nonT if v != x]
        assert len(rest) == 2 * (m - 2)
        for j, C in enumerate(cyc[2:]):
            a, b = rest[2 * j], rest[2 * j + 1]
            C = C[:-1]
            ia = C.index(a)
            C = C[ia:] + C[:ia]
            ib = C.index(b)
            paths += [C[: ib + 1], C[ib:] + [a]]
    else:
        m = N // 2
        Z = zigzag(m)
        ends = [(P[0], P[-1]) for P in Z]
        order = [ends[0][0], ends[0][1], ends[1][0], ends[1][1]] + \
            [v for v in range(N) if v not in ends[0] + ends[1]]
        lab = {v: i for i, v in enumerate(order)}
        Z = [[lab[v] for v in P] for P in Z]
        mu = [(P[0], P[-1]) for P in Z[2:]]           # perfect matching of S - T
        S = nx.complete_graph(N)
        S.remove_edges_from(mu)
        paths = []
        cut = set(frozenset(e) for e in mu)
        for P in Z:
            cur = [P[0]]
            for a, b in zip(P, P[1:]):
                if frozenset((a, b)) in cut:
                    paths.append(cur)
                    cur = [b]
                else:
                    cur.append(b)
            paths.append(cur)
    # check the realisation of b' = 1 on T, 2 elsewhere
    used = [frozenset(e) for P in paths for e in zip(P, P[1:])]
    assert all(len(set(P)) == len(P) and len(P) >= 2 for P in paths)
    assert len(used) == len(set(used)) == S.number_of_edges() and all(S.has_edge(*tuple(e)) for e in used)
    endc = {v: 0 for v in S}
    for P in paths:
        endc[P[0]] += 1
        endc[P[-1]] += 1
    assert all(endc[v] == (1 if v < 4 else 2) for v in S), endc
    return S, paths


def ham_decomposition(LG):
    n = LG.number_of_nodes()
    allE = frozenset(frozenset(e) for e in LG.edges())
    cycles = {}

    def dfs(path, used):
        u = path[-1]
        if len(path) == n:
            if LG.has_edge(u, path[0]):
                cycles[frozenset(frozenset((path[i], path[(i + 1) % n])) for i in range(n))] = list(path)
            return
        for w in LG[u]:
            if w not in used:
                used.add(w)
                path.append(w)
                dfs(path, used)
                path.pop()
                used.discard(w)

    dfs([0], {0})
    for c, p in cycles.items():
        if (allE - c) in cycles:
            return p, cycles[allE - c]
    return None


def build(H):
    LG = nx.convert_node_labels_to_integers(nx.line_graph(H))
    w = 0
    us = sorted(LG[w])
    N = LG.number_of_nodes() - 1
    S, Spaths = surplus_clique(N)
    G = nx.Graph()
    G.add_edges_from((("R", a), ("R", c)) for a, c in LG.edges() if w not in (a, c))
    G.add_edges_from((("S", a), ("S", c)) for a, c in S.edges())
    for i, u in enumerate(us):
        G.add_edge(("R", u), ("S", i))           # u_{i+1} -- t_{i+1}
    return G, LG, w, us, Spaths


def realisation(G, LG, w, us, Spaths):
    dec = ham_decomposition(LG)
    if dec is None:
        return None
    t = {u: ("S", i) for i, u in enumerate(us)}
    paths = []
    for C in dec:
        i = C.index(w)
        C = C[i + 1:] + C[:i]                     # the cycle without w, from one u to another
        paths.append([t[C[0]]] + [("R", v) for v in C] + [t[C[-1]]])
    paths += [[("S", v) for v in P] for P in Spaths]
    used = [frozenset(e) for P in paths for e in zip(P, P[1:])]
    assert all(len(set(P)) == len(P) for P in paths)
    assert len(used) == len(set(used)) == G.number_of_edges() and all(G.has_edge(*tuple(e)) for e in used)
    endc = {v: 0 for v in G}
    for P in paths:
        endc[P[0]] += 1
        endc[P[-1]] += 1
    assert all(endc[v] == (2 if v[0] == "S" else 0) for v in G)
    return paths


def main():
    for N in range(6, 30):
        surplus_clique(N)
    print("surplus clique S_N: explicit realisation of (1 on T, 2 elsewhere) valid for 6 <= N <= 29")
    rng = random.Random(7)
    tests = [("prism", nx.circular_ladder_graph(3)), ("K33", nx.complete_bipartite_graph(3, 3)),
             ("cube", nx.hypercube_graph(3)), ("Petersen", nx.petersen_graph())]
    B = nx.Graph()
    for off in (0, 5):
        B.add_edges_from([(off + a, off + c) for a, c in [(0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 4), (4, 1)]])
    B.add_edge(4, 9)
    tests.append(("bridged", B))
    for i in range(5):
        tests.append((f"random cubic {2 * (4 + i)}", nx.random_regular_graph(3, 2 * (4 + i), seed=rng.randrange(10**6))))
    for name, H in tests:
        if not nx.is_connected(H):
            continue
        H = nx.convert_node_labels_to_integers(H)
        bridgeless = not any(True for _ in nx.bridges(H))
        G, LG, w, us, Spaths = build(H)
        deg = dict(G.degree())
        n = G.number_of_nodes()
        M = {v for v in G if v[0] == "S"}
        assert all(d % 2 == 0 for d in deg.values()) and min(deg.values()) >= 4 and 2 * len(M) == n
        lam = nx.edge_connectivity(G)
        cf = cut_feasible_flow(G, M)
        line = (f"{name:16s} n={n:3d} min deg {min(deg.values())} bridgeless={bridgeless!s:5s} "
                f"edge-conn {lam} M cut-feasible={cf!s:5s}")
        assert cf == bridgeless and (lam >= 4) == bridgeless, line
        ham = hamiltonian(H)
        if LG.number_of_nodes() <= 24:
            R = realisation(G, LG, w, us, Spaths)
            line += f" H Hamiltonian={ham!s:5s} explicit realisation={R is not None}"
            assert (R is not None) == ham
        if n <= 16:
            Gi = nx.convert_node_labels_to_integers(G, label_attribute="old")
            real = realis.profile_ok(Gi, {v: 2 if Gi.nodes[v]["old"][0] == "S" else 0 for v in Gi})
            line += f" oracle realisable={real}"
            assert real == ham
        print(line, flush=True)
    print("OK")


if __name__ == "__main__":
    main()

"""EMM fails at every minimum degree and edge-connectivity: the graphs G_r (r >= 2).

Construction (manuscript, section "Forcing gadgets", Theorem "EMM fails in every connectivity
class"):
  M_r   the 2r-regular multigraph on the cycle c_0 ... c_{2r-1} (side c_i c_{i+1} has
        multiplicity r-1 for even i and r for odd i) plus a vertex w joined once to every c_i;
  D_r   M_r - w with every odd c_i blown up into a block K_{2r}: each of the 2r edges at c_i
        goes to its own vertex of the block.  Its 2r ports are the ends of the former w-edges.
        Every vertex of D_r has degree 2r in the host graph, and b = 0 on D_r;
  G_r   D_r plus a block S_r of |D_r| vertices, all of even degree and all marked (b = 2); the
        ports of c_0 and c_1 go to one vertex s of S_r, the other ports to distinct t_i.

Checks:
  1. the Hamiltonian decompositions of M_r all pair c_{2j} with c_{2j+1} at w (brute force);
  2. K_{2r} has, for every perfect matching of its vertices, a decomposition into r Hamiltonian
     paths with these end pairs (brute force);
  3. an explicit realisation of D_r^+ (D_r plus one temporary leaf per port), assembled from 1
     and 2, is valid (it is used in the manuscript's proof of cut-feasibility);
  4. for r = 2, the oracle tools/realis.c: D_2^+ is realisable, and no realisation separates the
     leaves of c_0 and c_1;
  5. G_r: minimum degree 2r, edge-connectivity 2r, M = V(S_r) is a half-set, cut-feasible by the
     arm form (max-flow; Lemma "four forms" (d)) and, for r = 2, by gemm_test.feasible and
     cut_test.cut_ok as well.
Non-realisability of G_r is the gluing argument of the manuscript.

Usage: python3 manuscripts/endpoint-min-max/scripts/emm_connectivity.py [r ...]   (default 2 3)
"""
import os
import sys
from itertools import combinations, permutations

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.normpath(os.path.join(HERE, "..", "..", "..", "tools"))
sys.path.insert(0, TOOLS)


def mult(r, i):
    return r - 1 if i % 2 == 0 else r


def multigraph_decompositions(r):
    """All Hamiltonian decompositions of M_r into r Hamiltonian cycles, as lists of sets of
    (side or w-edge) labels; parallel copies are unlabelled (a cycle uses at most one copy)."""
    k = 2 * r
    # a Hamiltonian cycle of M_r passes w once; minus w it is a Hamiltonian path of the cycle
    # multigraph, i.e. the cycle minus one side j, from c_{j+1} round to c_j.
    paths = []
    for j in range(k):
        if mult(r, j) == 0:
            continue
        sides = frozenset(i for i in range(k) if i != j)
        paths.append((j, sides, frozenset({j, (j + 1) % k})))
    decs = []
    for combo in combinations(range(len(paths)), r):
        use = [0] * k
        endcount = [0] * k
        for t in combo:
            for i in paths[t][1]:
                use[i] += 1
            for c in paths[t][2]:
                endcount[c] += 1
        if all(use[i] == mult(r, i) for i in range(k)) and all(e == 1 for e in endcount):
            decs.append([paths[t] for t in combo])
    # combinations with repetition are impossible: two paths omitting the same side would use
    # every other side once more than allowed only if mult < r... check repetition explicitly
    from itertools import combinations_with_replacement
    rep = 0
    for combo in combinations_with_replacement(range(len(paths)), r):
        if len(set(combo)) == r:
            continue
        use = [0] * k
        for t in combo:
            for i in paths[t][1]:
                use[i] += 1
        if all(use[i] == mult(r, i) for i in range(k)):
            rep += 1
    return decs, rep


def kblock_free(r):
    """For every perfect matching of the 2r vertices of K_{2r}: a decomposition into r
    Hamiltonian paths whose end pairs are the matching.  Returns a dict matching -> paths."""
    k = 2 * r
    V = list(range(k))
    E = set(frozenset(e) for e in combinations(V, 2))
    hp = {}
    for perm in permutations(V):
        if perm[0] < perm[-1]:
            key = frozenset({perm[0], perm[-1]})
            hp.setdefault(key, []).append(frozenset(frozenset(e) for e in zip(perm, perm[1:])))

    def matchings(rest):
        if not rest:
            yield []
            return
        a = rest[0]
        for b in rest[1:]:
            for m in matchings([x for x in rest if x not in (a, b)]):
                yield [frozenset({a, b})] + m

    out = {}
    for mt in matchings(V):
        def rec(i, used, chosen):
            if i == len(mt):
                return list(chosen) if used == E else None
            for P in hp[mt[i]]:
                if not (P & used):
                    res = rec(i + 1, used | P, chosen + [P])
                    if res:
                        return res
            return None
        sol = rec(0, frozenset(), [])
        assert sol, ("K_%d not free for" % k, mt)
        out[frozenset(mt)] = sol
    return out


def build(r):
    """D_r and its ports; vertex names: ('c', i) for even i, ('B', i, x) for odd i, 0 <= x < 2r."""
    k = 2 * r
    D = nx.Graph()
    port = {}
    # block vertex roles at odd i: x in [0, r-2] -> towards c_{i-1}; [r-1, 2r-2] -> c_{i+1};
    # 2r-1 -> port
    for i in range(1, k, 2):
        D.add_edges_from((("B", i, x), ("B", i, y)) for x, y in combinations(range(k), 2))
        port[i] = ("B", i, k - 1)
        for x in range(r - 1):
            D.add_edge(("B", i, x), ("c", (i - 1) % k))
        for x in range(r - 1, k - 1):
            D.add_edge(("B", i, x), ("c", (i + 1) % k))
    for i in range(0, k, 2):
        port[i] = ("c", i)
    return D, port


def realisation(r, D, port, kfree):
    """Explicit realisation of D_r^+: r paths, leaf ('l', i) at port i."""
    k = 2 * r
    decs, _ = multigraph_decompositions(r)
    dec = decs[0]
    # assign copies: for side i, the paths using it get distinct copies (block vertices)
    paths = []
    copy_of = {}  # (path index, side) -> block vertex index used
    for i in range(k):
        users = [t for t, (j, sides, _) in enumerate(dec) if i in sides]
        assert len(users) == mult(r, i)
        odd = i if i % 2 == 1 else (i + 1) % k        # the blown-up endpoint of side i
        if odd == i:   # side c_i c_{i+1} with c_i blown up: copies r-1 .. 2r-2
            base = r - 1
        else:          # side c_i c_{i+1} with c_{i+1} blown up: copies 0 .. r-2
            base = 0
        for idx, t in enumerate(users):
            copy_of[(t, i)] = base + idx
    for t, (j, sides, ends) in enumerate(dec):
        # cycle order c_{j+1}, c_{j+2}, ..., c_j
        order = [(j + 1 + s) % k for s in range(k)]
        # block entry/exit vertices: for odd c, (in-vertex, out-vertex)
        seq = [("l", order[0])]
        for pos, c in enumerate(order):
            prev_side = None if pos == 0 else (order[pos - 1] if (order[pos - 1] + 1) % k == c else c)
            next_side = None if pos == k - 1 else c
            if c % 2 == 0:
                seq.append(("c", c))
            else:
                x_in = (k - 1) if pos == 0 else copy_of[(t, (c - 1) % k)]
                x_out = (k - 1) if pos == k - 1 else copy_of[(t, c)]
                seq.append(("Bin", c, x_in, x_out))
        seq.append(("l", order[-1]))
        paths.append(seq)
    # expand blocks: for each block, the matching of (x_in, x_out) over the r paths
    block_paths = {}
    for i in range(1, k, 2):
        mt = []
        for seq in paths:
            for it in seq:
                if it[0] == "Bin" and it[1] == i:
                    mt.append(frozenset({it[2], it[3]}))
        sol = kfree[frozenset(mt)]
        block_paths[i] = {}
        for P in sol:
            ends = [v for v in range(k) if sum(1 for e in P if v in e) == 1]
            block_paths[i][frozenset(ends)] = P
    out = []
    for seq in paths:
        Q = []
        for it in seq:
            if it[0] == "l":
                Q.append(("l", it[1]))
            elif it[0] == "c":
                Q.append(it)
            else:
                _, i, x_in, x_out = it
                P = block_paths[i][frozenset({x_in, x_out})]
                adj = {}
                for e in P:
                    a, b = tuple(e)
                    adj.setdefault(a, []).append(b)
                    adj.setdefault(b, []).append(a)
                walk = [x_in]
                while walk[-1] != x_out:
                    nxt = [y for y in adj[walk[-1]] if y not in walk]
                    walk.append(nxt[0])
                Q.extend(("B", i, x) for x in walk)
        out.append(Q)
    return out


def check_realisation(D, port, paths, r):
    Dl = D.copy()
    for i, x in port.items():
        Dl.add_edge(x, ("l", i))
    used = []
    for Q in paths:
        assert len(set(Q)) == len(Q), "not a path"
        for a, b in zip(Q, Q[1:]):
            assert Dl.has_edge(a, b), (a, b)
            used.append(frozenset((a, b)))
    assert len(used) == len(set(used)) == Dl.number_of_edges(), "not a partition"
    pairs = sorted(tuple(sorted((Q[0][1], Q[-1][1]))) for Q in paths)
    return pairs


def host(r, D, port):
    """D_r plus S_r = K_N (N = |D_r|) on new vertices, with the port edges; parities are fixed
    afterwards by fix_parity."""
    k = 2 * r
    N = D.number_of_nodes()
    G = D.copy()
    S = [("S", i) for i in range(N)]
    G.add_edges_from(combinations(S, 2))
    s = S[0]
    G.add_edge(s, port[0])
    G.add_edge(s, port[1])
    for i in range(2, k):
        G.add_edge(S[i - 1], port[i])
    return G, S


def fix_parity(G, S):
    """Make every vertex of S even by removing a matching on the odd ones (inside S)."""
    odd = [x for x in S if G.degree(x) % 2]
    while odd:
        a = odd.pop()
        for b in odd:
            if G.has_edge(a, b):
                G.remove_edge(a, b)
                odd.remove(b)
                break
        else:
            raise RuntimeError("cannot fix parity")
    return G


def arm_form_ok(G, b):
    for v in G:
        F = nx.DiGraph()
        for x, y in G.edges():
            if v in (x, y):
                continue
            F.add_edge(x, y, capacity=1)
            F.add_edge(y, x, capacity=1)
        for y in G[v]:
            F.add_edge("src", y, capacity=1)
        for z in G:
            if z != v and b[z] > 0:
                F.add_edge(z, "snk", capacity=b[z])
        if nx.maximum_flow_value(F, "src", "snk") != G.degree(v):
            return False, v
    return True, None


def main(rs):
    for r in rs:
        k = 2 * r
        print(f"=== r = {r}")
        decs, rep = multigraph_decompositions(r)
        pairings = {frozenset(frozenset(P[2]) for P in dec) for dec in decs}
        print(f"M_{r}: {len(decs)} Hamiltonian decomposition(s) (up to parallel copies), {rep} with a repeated cycle;"
              f" pairings at w: {[sorted(tuple(sorted(e)) for e in pr) for pr in pairings]}")
        assert len(decs) == 1 and rep == 0
        kfree = kblock_free(r)
        print(f"K_{k} free: all {len(kfree)} perfect matchings are end pairings of Hamiltonian path decompositions")
        D, port = build(r)
        assert all(D.degree(v) + (v in port.values()) == k for v in D)
        paths = realisation(r, D, port, kfree)
        pairs = check_realisation(D, port, paths, r)
        print(f"D_{r}: {D.number_of_nodes()} vertices, {D.number_of_edges()} edges; explicit realisation of D^+ valid,"
              f" leaf pairs {pairs}")
        if r == 2:
            import realis
            Dl = D.copy()
            b = {v: 0 for v in D}
            for i, x in port.items():
                Dl.add_edge(x, ("l", i))
                b[("l", i)] = 1
            H = nx.convert_node_labels_to_integers(Dl, label_attribute="old")
            bH = {v: b[H.nodes[v]["old"]] for v in H}
            tot = realis.profile_ok(H, bH)
            Ds = D.copy()
            bs = {v: 0 for v in D}
            Ds.add_edge(port[0], "s"); Ds.add_edge(port[1], "s"); bs["s"] = 2
            for i in (2, 3):
                Ds.add_edge(port[i], ("l", i)); bs[("l", i)] = 1
            H2 = nx.convert_node_labels_to_integers(Ds, label_attribute="old")
            sep = realis.profile_ok(H2, {v: bs[H2.nodes[v]["old"]] for v in H2})
            print(f"realis.c: D_2^+ realisable {tot}; leaves of c_0, c_1 on different paths possible: {sep}")
            assert tot and not sep
        G, S = host(r, D, port)
        G = fix_parity(G, S)
        deg = dict(G.degree())
        n = G.number_of_nodes()
        assert all(deg[x] % 2 == 0 for x in G)
        Ev = list(G)
        M = set(S)
        assert 2 * len(M) == len(Ev)
        b = {v: 2 if v in M else 0 for v in G}
        assert sum(b.values()) == n
        lam = nx.edge_connectivity(G)
        kap = nx.node_connectivity(G)
        print(f"G_{r}: n = {n}, m = {G.number_of_edges()}, min degree {min(deg.values())}, edge-connectivity {lam},"
              f" vertex-connectivity {kap}; all degrees even; M = V(S_{r}) is a half-set")
        assert min(deg.values()) >= k and lam >= k
        ok, wit = arm_form_ok(G, b)
        print(f"cut-feasible (arm form, max-flow at every vertex): {ok}")
        assert ok
        if n <= 20:
            import gemm_test
            import cut_test
            H = nx.convert_node_labels_to_integers(G, label_attribute="old")
            bH = {v: b[H.nodes[v]["old"]] for v in H}
            ok1, _ = gemm_test.feasible(gemm_test.prepare(H), [bH[v] for v in sorted(H)])
            ok2, _ = cut_test.cut_ok(cut_test.prepare(H), bH, n // 2)
            print(f"cut-feasible: gemm_test.feasible {ok1}, cut_test.cut_ok {ok2}")
            assert ok1 and ok2
            print("graph6:", nx.to_graph6_bytes(H, header=False).decode().strip(),
                  "M mask", sum(1 << v for v in H if H.nodes[v]["old"] in M))
    print("OK")


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]] or [2, 3])

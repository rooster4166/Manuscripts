"""EMM_3 is false: a cut-feasible, non-realisable half-set in a graph of minimum degree 3.

Checks for the manuscript's section "Forcing gadgets" (Theorem: EMM_3 is false):

  1. The gadget D (two K4 blocks A, B and two vertices p, q; ports p, b0; odd vertices a0, q)
     is joined-forcing for the profile b = 1 on a0, q and 0 elsewhere:
       (a) by the exact oracle tools/realis.c: D + l1 p + l2 b0 is realisable, but D + w
           (w adjacent to p and b0, b(w) = 2) is not;
       (b) by an independent brute force: every Hamiltonian decomposition of the 4-regular
           graph D' = D + w (w adjacent to p, b0, a0, q) pairs w p with w b0;
       (c) the explicit realisation of the manuscript is valid.
  2. The host graph G = D + S + s p + s b0 (S = K_{4,4}, s in S) has minimum degree 3, and the
     half-set M = V(S) is cut-feasible, by three implementations of the cut inequality
     (gemm_test.feasible, cut_test.cut_ok, tools/cutfeas.c) and by the arm form (max-flow).
  3. The outer side of the cut (K_{4,4} with two leaves at s) is realisable, so the obstruction
     is the pairing of the cut edges, not a non-realisable side.
  4. Non-realisability of G is the gluing argument of the manuscript (no computation needed);
     realis.c cannot run at n = 18 (tools/realis_wide.c confirms it, see outputs/).

Usage: python3 manuscripts/endpoint-min-max/scripts/emm3_counterexample.py
"""
import os
import subprocess
import sys
import tempfile
from itertools import combinations

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.normpath(os.path.join(HERE, "..", "..", "..", "tools"))
sys.path.insert(0, TOOLS)
import realis  # noqa: E402
import gemm_test  # noqa: E402
import cut_test  # noqa: E402

a0, a1, a2, a3, b0, b1, b2, b3, p, q = range(10)
NAMES = ["a0", "a1", "a2", "a3", "b0", "b1", "b2", "b3", "p", "q"]


def gadget():
    D = nx.Graph()
    D.add_edges_from(combinations([a0, a1, a2, a3], 2))
    D.add_edges_from(combinations([b0, b1, b2, b3], 2))
    D.add_edges_from([(p, a1), (p, a2), (p, b1), (q, a3), (q, b2), (q, b3)])
    return D


def check_gadget():
    D = gadget()
    bD = {v: 0 for v in D}
    bD[a0] = bD[q] = 1
    # (a) the oracle
    Dp = D.copy()
    Dp.add_edges_from([(p, 10), (b0, 11)])          # l1 = 10, l2 = 11
    tot = realis.profile_ok(Dp, {**bD, 10: 1, 11: 1})
    Dw = D.copy()
    Dw.add_edges_from([(p, 10), (b0, 10)])          # w = 10, b(w) = 2
    sep = realis.profile_ok(Dw, {**bD, 10: 2})
    print("D^+ realisable:", tot, "| separated realisation (D + w, b(w) = 2):", sep)
    assert tot and not sep
    # (b) Hamiltonian decompositions of D' = D + w, w adjacent to p, b0, a0, q
    Dq = D.copy()
    w = 10
    Dq.add_edges_from([(w, p), (w, b0), (w, a0), (w, q)])
    assert all(d == 4 for _, d in Dq.degree())
    E = [tuple(sorted(e)) for e in Dq.edges()]
    n = Dq.number_of_nodes()
    decs = []
    e0 = E[0]
    # every Hamiltonian cycle through e0, as an edge set, by depth-first search
    def ham_cycles():
        start, first = e0
        out = []
        def rec(path, vis):
            c = path[-1]
            if len(path) == n:
                if Dq.has_edge(c, start):
                    out.append(frozenset(tuple(sorted(e)) for e in zip(path, path[1:] + [start])))
                return
            for y in Dq[c]:
                if y not in vis:
                    rec(path + [y], vis | {y})
        rec([start, first], {start, first})
        return out
    for C in ham_cycles():
        rest = nx.Graph([e for e in E if e not in C])
        if rest.number_of_nodes() == n and nx.is_connected(rest) and all(d == 2 for _, d in rest.degree()):
            decs.append(C)
    trans = set()
    for C in decs:
        cyc_p = (min(w, p), max(w, p)) in C
        cyc_b0 = (min(w, b0), max(w, b0)) in C
        trans.add(cyc_p == cyc_b0)
    print("Hamiltonian decompositions of D':", len(decs), "| w p and w b0 always in one cycle:", trans == {True})
    assert decs and trans == {True}
    # (c) the explicit realisation P0, R of D^+
    P0 = ["l1", p, a2, a1, a0, a3, q, b3, b1, b2, b0, "l2"]
    R = [a0, a2, a3, a1, p, b1, b0, b3, b2, q]
    Dl = D.copy()
    Dl.add_edges_from([(p, "l1"), (b0, "l2")])
    used = []
    for P in (P0, R):
        assert len(set(P)) == len(P)
        for x, y in zip(P, P[1:]):
            assert Dl.has_edge(x, y)
            used.append(frozenset((x, y)))
    assert len(used) == len(set(used)) == Dl.number_of_edges()
    ends = sorted(map(str, [P0[0], P0[-1], R[0], R[-1]]))
    print("explicit realisation of D^+ valid; ends", ends)
    return D


def host(D):
    G = D.copy()
    s = 10
    S = list(range(10, 18))
    G.add_edges_from((x, y) for x in S[:4] for y in S[4:])        # K_{4,4}, s = 10
    G.add_edges_from([(s, p), (s, b0)])
    return G, S


def arm_form_ok(G, b):
    """Lemma (four forms) (d): an arm system at every vertex, by max-flow."""
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


def check_host(D):
    G, S = host(D)
    n = G.number_of_nodes()
    deg = dict(G.degree())
    print("G: n =", n, "m =", G.number_of_edges(), "min degree", min(deg.values()),
          "connected", nx.is_connected(G), "edge connectivity", nx.edge_connectivity(G))
    assert min(deg.values()) >= 3 and nx.is_connected(G) and n % 2 == 0
    Ev = [v for v in G if deg[v] % 2 == 0]
    M = set(S)
    assert M <= set(Ev) and 2 * len(M) == len(Ev)
    b = {v: 1 if deg[v] % 2 else (2 if v in M else 0) for v in G}
    assert sum(b.values()) == n
    print("half-set M = V(S), |Ev| =", len(Ev), "; odd vertices:", [NAMES[v] for v in G if deg[v] % 2])
    nodes = sorted(G)
    ok1, wit1 = gemm_test.feasible(gemm_test.prepare(G), [b[v] for v in nodes])
    ok2, wit2 = cut_test.cut_ok(cut_test.prepare(G), b, n // 2)
    # tools/cutfeas.c: all cut-feasible half-sets
    binp = os.path.join(tempfile.gettempdir(), "cutfeas_bin")
    subprocess.check_call(["gcc", "-O2", "-o", binp, os.path.join(TOOLS, "cutfeas.c")])
    line = f"{n} {G.number_of_edges()} " + " ".join(f"{x} {y}" for x, y in G.edges()) + "\n"
    out = subprocess.run([binp], input=line, capture_output=True, text=True, check=True).stdout.split()
    masks = set(map(int, out[1:]))
    mM = sum(1 << v for v in M)
    ok3 = mM in masks
    ok4, wit4 = arm_form_ok(G, b)
    print("cut-feasible: gemm_test.feasible", ok1, "| cut_test.cut_ok", ok2, "| cutfeas.c", ok3,
          f"({out[0]} cut-feasible half-sets in all)", "| arm form (max-flow)", ok4)
    assert ok1 and ok2 and ok3 and ok4
    # the outer side of the cut {sp, sb0}: K_{4,4} with two leaves at s, b = 2 on K_{4,4}
    O = G.subgraph(S).copy()
    O.add_edges_from([(10, "l1"), (10, "l2")])
    bO = {v: 2 for v in S}
    bO["l1"] = bO["l2"] = 1
    O2 = nx.convert_node_labels_to_integers(O, label_attribute="old")
    outer = realis.profile_ok(O2, {v: bO[O2.nodes[v]["old"]] for v in O2})
    print("outer side (K_{4,4} + two leaves at s) realisable:", outer)
    assert outer
    print("graph6 of G:", nx.to_graph6_bytes(G, header=False).decode().strip(),
          "M mask", mM)
    return G


if __name__ == "__main__":
    D = check_gadget()
    check_host(D)
    print("OK: EMM_3 counterexample verified (non-realisability: gluing argument of the manuscript)")

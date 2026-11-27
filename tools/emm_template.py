"""The inductive template for EMM (general profiles), tested exhaustively.

Let (G, b) be cut-feasible: b = d mod 2, sum b = 2p, and (L), (C) of tools/gemm_test.py hold.
For an edge uv put H = G - uv. The single-edge moves re-insert uv into a partition of H:
  NP     new path uv:                 b' = b - e_u - e_v  (p' = p - 1), needs b(u), b(v) >= 1;
  T(u>v) Fan transfer towards v:      b' = b + e_u - e_v  (p' = p),     needs b(v) >= 1 and
         b'(u) > |Z(v)|, where Z(v) = {w in N_H(v) : b'(w) = 0} (Fan's lemma, single edge).
  C      concatenation: uv joins a path ending at u to a different path ending at v:
         b' = b + e_u + e_v (p' = p + 1), needs b'(u) >= 2 or b'(v) >= 2 (then some path ending
         at one of them differs from a path ending at the other).
  NP_L   path insertion (option "peelL", L >= 2): delete the edges of a path P of length 2..L
         with ends a != z, b(a), b(z) >= 1; b' = b - e_a - e_z on G - E(P) (p' = p - 1).
         It always succeeds: P is added as a new path.
A move is *valid* if b' is cut-feasible on H. By Fan's lemma a valid move succeeds for every
partition of H with profile b'. So if every cut-feasible (G, b) with E(G) nonempty has a valid
move, cut-feasibility is an invariant and EMM (general profiles) follows by induction on |E|.

Option "star": also allow deleting all edges uT at a vertex u for a set T of h >= 2 neighbours
and re-inserting them by one grouped transfer (Fan's Lemma 3.3), which needs every donor outcome
to be cut-feasible: b'_t = b + e_t - e_u ... (not used by default).

Option "reduced": test only instances that survive the reductions valid in a minimal counterexample
(manuscript, Lemma R): no degree-2 vertex w with b(w) = 0 whose neighbours are non-adjacent
(smoothing), and no leaf w whose neighbour x has b(x) <= d(x) - 2 (leaf transfer).

Option "atleasthalf": the class EMM+ of connected G with p >= ceil(n/2) (the Gallai budget or
more). A move is then valid only if every component C of H with an edge has
sum_C b' >= |V(C)| (so it is again in the class), besides being cut-feasible. The general-profile
extension of EMM is false at n = 7, p = 2 (tools/gemm_test.py), below this class.

Option "diag": for each stuck instance, count the moves that are cut-feasible (and in the class)
but lack only their profile-level guarantee: transfers at Fan's equality (b'(u) = |Z(v)|),
concatenations with b'(u) = b'(v) = 1, and (with atleasthalf) path insertions that leave the class.

Usage: python3 tools/emm_template.py FILE.g6 [maxshow] [reduced] [peelL] [atleasthalf] [diag]
Prints the instances with no valid single-edge move ("STUCK") and a tally.
"""
import sys

import networkx as nx

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from gemm_test import prepare, feasible, profiles  # noqa: E402


def paths_upto(G, L):
    """All paths with 2..L edges, as vertex lists, each once (first vertex < last vertex)."""
    out = []

    def ext(path):
        if len(path) >= 3 and path[0] < path[-1]:
            out.append(list(path))
        if len(path) == L + 1:
            return
        for w in G[path[-1]]:
            if w not in path:
                path.append(w); ext(path); path.pop()
    for v in G:
        ext([v])
    return out


def in_class(H, b1):
    for C in nx.connected_components(H):
        if len(C) > 1 and sum(b1[v] for v in C) < len(C):
            return False
    return True


def moves(G, bb, peel=1, pmin=0):
    """Yield (edge, kind) for every valid move of the cut-feasible profile bb.
    pmin > 0 selects the class EMM+ (see the module docstring)."""
    def ok(H, b1):
        return (not pmin or in_class(H, b1)) and feasible(prepare(H), b1)[0]
    can_np = True
    if peel >= 2 and can_np:
        for P in paths_upto(G, peel):
            a, z = P[0], P[-1]
            if bb[a] >= 1 and bb[z] >= 1:
                H = G.copy(); H.remove_edges_from(zip(P, P[1:]))
                b1 = list(bb); b1[a] -= 1; b1[z] -= 1
                if ok(H, b1):
                    yield tuple(P), f"NP{len(P) - 1}"
    for u, v in G.edges():
        H = G.copy(); H.remove_edge(u, v)
        if bb[u] >= 1 and bb[v] >= 1 and can_np:
            b1 = list(bb); b1[u] -= 1; b1[v] -= 1
            if ok(H, b1):
                yield (u, v), "NP"
        for a, c in ((u, v), (v, u)):  # end moves from a to c; in H the end is at a
            if bb[c] >= 1:
                b1 = list(bb); b1[a] += 1; b1[c] -= 1
                Z = sum(1 for w in H[c] if b1[w] == 0)
                if b1[a] > Z and ok(H, b1):
                    yield (a, c), "T"
        b1 = list(bb); b1[u] += 1; b1[v] += 1
        if max(b1[u], b1[v]) >= 2 and ok(H, b1):
            yield (u, v), "C"


def reducible(G, bb):
    for w in G:
        d = G.degree(w)
        if d == 2 and bb[w] == 0:
            x, y = list(G[w])
            if not G.has_edge(x, y):
                return "smooth"
        if d == 1:
            x = next(iter(G[w]))
            if bb[x] <= G.degree(x) - 2:
                return "leaf"
    return None


def near_moves(G, bb, inclass):
    """Moves of a stuck instance that fail only their guarantee (see option diag)."""
    eq = cc = np_out = 0
    for u, v in G.edges():
        H = G.copy(); H.remove_edge(u, v)
        prep = prepare(H)
        ok = lambda b1: feasible(prep, b1)[0] and (not inclass or in_class(H, b1))
        for a, c in ((u, v), (v, u)):
            if bb[c] >= 1:
                b1 = list(bb); b1[a] += 1; b1[c] -= 1
                Z = sum(1 for w in H[c] if b1[w] == 0)
                if b1[a] == Z and ok(b1):
                    eq += 1
        b1 = list(bb); b1[u] += 1; b1[v] += 1
        if b1[u] == b1[v] == 1 and ok(b1):
            cc += 1
        if inclass and bb[u] >= 1 and bb[v] >= 1:
            b1 = list(bb); b1[u] -= 1; b1[v] -= 1
            if feasible(prep, b1)[0] and not in_class(H, b1):
                np_out += 1
    return eq, cc, np_out


def main():
    path = sys.argv[1]
    maxshow = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    reduced = "reduced" in sys.argv[3:]
    peel = max([int(a[4:]) for a in sys.argv[3:] if a.startswith("peel")] or [1])
    half = "atleasthalf" in sys.argv[3:]
    diag = "diag" in sys.argv[3:]
    graphs = nx.read_graph6(path)
    if not isinstance(graphs, list):
        graphs = [graphs]
    tally = dict(instances=0, stuck=0)
    shown = 0
    for G in graphs:
        G = nx.convert_node_labels_to_integers(G)
        prep = prepare(G)
        for bb in profiles(prep[1]):
            n = G.number_of_nodes()
            if sum(bb) == 0 or (half and sum(bb) < n) or not feasible(prep, list(bb))[0]:
                continue
            if reduced and reducible(G, bb):
                tally["reducible"] = tally.get("reducible", 0) + 1
                continue
            tally["instances"] += 1
            kinds = {k for _, k in moves(G, bb, peel, 1 if half else 0)}
            if not kinds:
                tally["stuck"] += 1
                extra = ""
                if diag:
                    eq, cc, npo = near_moves(G, bb, half)
                    extra = f" fan_equality {eq} concat_1_1 {cc} np_leaves_class {npo}"
                    key = "diag:" + ("eq" if eq else "") + ("cc" if cc else "") + ("npout" if npo else "")
                    tally[key] = tally.get(key, 0) + 1
                if shown < maxshow:
                    shown += 1
                    print("STUCK", nx.to_graph6_bytes(G, header=False).decode().strip(),
                          sorted(G.edges()), "b", bb, extra, flush=True)
            else:
                key = "+".join(sorted(kinds))
                tally[key] = tally.get(key, 0) + 1
    print(tally, flush=True)


if __name__ == "__main__":
    main()

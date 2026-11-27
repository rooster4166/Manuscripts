"""Is cut-feasibility the only obstruction to realising a half-set of even vertices?

For a connected graph G of even order n = 2k with even-vertex set Ev (|Ev| = e), a half-set M
(|M| = e/2) determines the simple profile b: 1 on odd vertices, 2 on M, 0 on Ev \\ M (sum 2k).
Necessary conditions for b to be realised by k paths:
  (L)  b(v) <= d(v) and d(v) + b(v) <= 2k for every v;
  (C)  even-degrees.pdf, Section 12.4, inequality (1): for every v and every W subset of V - v,
           b(W) <= |delta(W)| + 2k - d(v) - b(v).
Question (EMM): is every half-set satisfying (L) and (C) realisable?

Usage: python3 tools/cut_test.py FILE.g6 [limit]
Reports graphs with a half-set that satisfies (L) and (C) but is not realisable ("EMM fails"),
and checks that realisable half-sets always satisfy (C) (soundness of the inequality).
"""
import sys
from itertools import combinations

import networkx as nx

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import realis  # noqa: E402


def prepare(G):
    """Per-graph data: node order, degrees, and |delta(W)| for every vertex set W (bitmask)."""
    nodes = list(G.nodes())
    n = len(nodes)
    idx = {v: i for i, v in enumerate(nodes)}
    nbr = [0] * n
    for a, c in G.edges():
        nbr[idx[a]] |= 1 << idx[c]
        nbr[idx[c]] |= 1 << idx[a]
    cut = [0] * (1 << n)
    for W in range(1, 1 << n):
        low = (W & -W).bit_length() - 1
        Wp = W & ~(1 << low)
        # adding vertex low to Wp: edges to Wp stop crossing, edges outside start crossing
        inside = bin(nbr[low] & Wp).count("1")
        cut[W] = cut[Wp] + (bin(nbr[low]).count("1") - inside) - inside
    deg = [G.degree(v) for v in nodes]
    return nodes, idx, deg, cut


def cut_ok(prep, b, k):
    nodes, idx, deg, cut = prep
    n = len(nodes)
    bb = [b[v] for v in nodes]
    slack = [2 * k - deg[i] - bb[i] for i in range(n)]
    if min(slack) < 0:
        return False, ("local", None)
    full = (1 << n) - 1
    # bW over all W incrementally
    bW = [0] * (1 << n)
    for W in range(1, 1 << n):
        low = (W & -W).bit_length() - 1
        bW[W] = bW[W & ~(1 << low)] + bb[low]
    for W in range(1, full):
        excess = bW[W] - cut[W]
        if excess <= 0:
            continue
        outside = full & ~W
        m = min(slack[i] for i in range(n) if outside >> i & 1)
        if excess > m:
            return False, ([nodes[i] for i in range(n) if W >> i & 1])
    return True, None


def main():
    path = sys.argv[1]
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 10**9
    graphs = nx.read_graph6(path)
    if not isinstance(graphs, list):
        graphs = [graphs]
    tested = fails = unsound = halfsets = nonreal = 0
    for G in graphs[:limit]:
        n = G.number_of_nodes()
        if n % 2 or not nx.is_connected(G):
            continue
        k = n // 2
        Ev, fam = realis.family(G)
        e = len(Ev)
        if e < 2:
            continue
        famset = set(fam)
        prep = prepare(G)
        tested += 1
        for M in combinations(Ev, e // 2):
            halfsets += 1
            M = frozenset(M)
            b = {v: (G.degree(v) % 2) for v in G}
            for v in M:
                b[v] = 2
            loc = all(b[v] <= G.degree(v) and G.degree(v) + b[v] <= 2 * k for v in G)
            ok, wit = cut_ok(prep, b, k)
            real = M in famset
            nonreal += (not real)
            if real and not (ok and loc):
                unsound += 1
                print("UNSOUND", nx.to_graph6_bytes(G, header=False).strip().decode(), sorted(M), wit,
                      flush=True)
            if not real and ok and loc:
                fails += 1
                print("EMM-FAIL", nx.to_graph6_bytes(G, header=False).strip().decode(),
                      sorted(G.edges()), "Ev", Ev, "M", sorted(M), flush=True)
    print(f"tested {tested} graphs, {halfsets} half-sets ({nonreal} non-realisable, all must be cut-excluded): {fails} EMM failures, {unsound} unsound",
          flush=True)


if __name__ == "__main__":
    main()

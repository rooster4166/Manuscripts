"""Does the cut criterion of EMM extend to general profiles?

For a graph G and a profile b : V -> N with b = d mod 2 and sum b = 2p, a partition of E(G)
into p paths with exactly b(v) ends at v exists only if
  (L)  b(v) <= d(v) and d(v) + b(v) <= 2p for every v;
  (C)  for every v and every W subset of V - v:  b(W) <= |delta(W)| + 2p - d(v) - b(v)
       (even-degrees.pdf, Section 12.4, inequality (1), with k replaced by p).
EMM asserts sufficiency for the simple profiles of a half-set (p = n/2). An induction on |E|
deletes an edge and so needs general profiles. This script tests sufficiency for every profile
b <= d with the right parity, on every graph of a graph6 file.

Usage: python3 tools/gemm_test.py FILE.g6 [maxfail] [half] [sample=N,seed=S]
  half      only profiles with p = n/2 (n even): the class kept by edge deletion plus transfer
  sample=N  only N graphs of the file, chosen at random with the given seed
  pmax=P    only profiles with p <= P (the low-budget side, where the n = 7 failure lies)
Prints each failure (cut-feasible, not realisable) and a tally; "unsound" counts realisable
profiles violating (L) or (C) and must be 0.
"""
import sys
from itertools import product

import networkx as nx

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import realis  # noqa: E402


def prepare(G):
    nodes = sorted(G.nodes())
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
        inside = bin(nbr[low] & Wp).count("1")
        cut[W] = cut[Wp] + bin(nbr[low]).count("1") - 2 * inside
    deg = [bin(x).count("1") for x in nbr]
    return nodes, deg, cut


def feasible(prep, bb):
    """(L) and (C) for the profile bb (list in node order). Returns (ok, witness)."""
    nodes, deg, cut = prep
    n = len(nodes)
    p2 = sum(bb)
    if p2 % 2:
        return False, "odd sum"
    slack = [p2 - deg[i] - bb[i] for i in range(n)]
    for i in range(n):
        if bb[i] > deg[i] or slack[i] < 0 or (bb[i] - deg[i]) % 2:
            return False, ("local", i)
    full = (1 << n) - 1
    bW = [0] * (1 << n)
    for W in range(1, 1 << n):
        low = (W & -W).bit_length() - 1
        bW[W] = bW[W & ~(1 << low)] + bb[low]
        excess = bW[W] - cut[W]
        if excess <= 0 or W == full:
            continue
        out = full & ~W
        m = min(slack[i] for i in range(n) if out >> i & 1)
        if excess > m:
            return False, ("cut", W)
    return True, None


def profiles(deg):
    return product(*[range(d % 2, d + 1, 2) for d in deg])


def main():
    path = sys.argv[1]
    maxfail = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    half = "half" in sys.argv[3:]
    pmax = min([int(a[5:]) for a in sys.argv[3:] if a.startswith("pmax=")] or [10**9])
    graphs = nx.read_graph6(path)
    if not isinstance(graphs, list):
        graphs = [graphs]
    for a in sys.argv[3:]:
        if a.startswith("sample="):
            import random
            kv = dict(x.split("=") for x in a.split(","))
            random.seed(int(kv.get("seed", 1)))
            graphs = random.sample(graphs, int(kv["sample"]))
    tally = dict(graphs=0, profiles=0, feasible=0, realisable=0, fail=0, unsound=0)
    shown = 0
    for G in graphs:
        G = nx.convert_node_labels_to_integers(G)
        prep = prepare(G)
        tally["graphs"] += 1
        n = G.number_of_nodes()
        for bb in profiles(prep[1]):
            if sum(bb) == 0 or (half and sum(bb) != n) or sum(bb) > 2 * pmax:
                continue
            tally["profiles"] += 1
            ok, _ = feasible(prep, list(bb))
            real = realis.profile_ok(G, {v: bb[v] for v in G})
            tally["feasible"] += ok
            tally["realisable"] += real
            if ok and not real:
                tally["fail"] += 1
                key = f"fail_p{sum(bb) // 2}"
                tally[key] = tally.get(key, 0) + 1
                if shown < maxfail:
                    shown += 1
                    print("FAIL", nx.to_graph6_bytes(G, header=False).decode().strip(),
                          sorted(G.edges()), "b", bb, flush=True)
            if real and not ok:
                tally["unsound"] += 1
                print("UNSOUND", nx.to_graph6_bytes(G, header=False).decode().strip(), bb)
    print(tally, flush=True)


if __name__ == "__main__":
    main()

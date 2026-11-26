"""Exact partition checks for audit A12, on top of the audit's own DFS solver
research/audit/A11-scripts/exact.py (no code from the authors' scripts or tools/).

  critical(G)      : True iff G (even order n) has no partition into at most n/2 - 1 paths.
  realisable(G, S) : a partition with b = 1 on odd vertices, 2 on S, 0 on the other even vertices.
  rooted(G, r)     : a partition into at most n/2 paths with an end at r.
Usage: python3 partitions.py crit FILE          (criticality of each graph6 line)
       python3 partitions.py ex53               (endpoint-structure Example 53)
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "A11-scripts"))
import exact  # noqa: E402
import networkx as nx  # noqa: E402


def adj(G):
    return {v: set(G[v]) for v in G}


def has_partition_le(G, k):
    """Some partition into at most k paths (searched over all end vectors with sum <= 2k)."""
    A = adj(G)
    deg = {v: len(A[v]) for v in A}
    base = {v: deg[v] % 2 for v in A}
    slack = 2 * k - sum(base.values())
    if slack < 0:
        return None
    verts = [v for v in A if deg[v] > 0]
    for extra in range(0, slack // 2 + 1):
        for combo in itertools.combinations_with_replacement(verts, extra):
            beta = dict(base)
            for w in combo:
                beta[w] += 2
            if any(beta[w] > deg[w] for w in A):
                continue
            P = exact.realise(A, beta)
            if P is not None:
                assert exact.check_partition(A, P, beta)
                return P
    return None


def critical(G):
    n = G.number_of_nodes()
    return has_partition_le(G, n // 2 - 1) is None


def realisable(G, S):
    A = adj(G)
    beta = {}
    for v in A:
        d = len(A[v])
        beta[v] = 1 if d % 2 else (2 if v in S else 0)
    P = exact.realise(A, beta)
    if P is not None:
        assert exact.check_partition(A, P, beta)
    return P


def rooted(G, r):
    A = adj(G)
    P = exact.floor_with_end(A, r, budget=G.number_of_nodes() // 2)
    if P is not None:
        assert exact.check_partition(A, P)
    return P


def ex53():
    G = nx.from_graph6_bytes(b"Gqz~vw")
    d = dict(G.degree())
    Ev = [v for v in G if d[v] % 2 == 0]
    print("Gqz~vw: Ev =", Ev, "N(3) =", sorted(G[3]), "critical:", critical(G))
    bad = [S for S in itertools.combinations(Ev, 3) if realisable(G, set(S)) is None]
    print("triples of even vertices:", len(list(itertools.combinations(Ev, 3))), "non-realisable:", bad)
    for e, want in (((3, 1), {5, 7}), ((3, 5), {1, 7}), ((3, 7), {1, 5})):
        K = G.copy(); K.remove_edge(*e)
        dk = dict(K.degree())
        EvK = [v for v in K if dk[v] % 2 == 0]
        pairs = list(itertools.combinations(EvK, 2))
        nonreal = [p for p in pairs if realisable(K, set(p)) is None]
        print(f"G - {e[0]}{e[1]}: Ev = {EvK}; non-realisable pairs: {nonreal}; "
              f"N_E(3) minus {e[1]} = {sorted(want)} realisable: {realisable(K, want) is not None}")
    # the simple profile of Cor 2.6 / Example 53: {0,3,7} and {0,3,5}
    for S in ({0, 3, 7}, {0, 3, 5}, {3, 5, 7}):
        print("realisable", sorted(S), ":", realisable(G, S))


if __name__ == "__main__":
    if sys.argv[1] == "crit":
        for line in open(sys.argv[2]):
            g = line.strip()
            if not g:
                continue
            G = nx.from_graph6_bytes(g.encode())
            P = has_partition_le(G, G.number_of_nodes() // 2 - 1)
            print(g, "critical" if P is None else f"noncritical {P}", flush=True)
    elif sys.argv[1] == "ex53":
        ex53()
    elif sys.argv[1] == "rooted":
        for line in open(sys.argv[2]):
            g = line.strip()
            if not g:
                continue
            G = nx.from_graph6_bytes(g.encode())
            out = [(r, rooted(G, r) is not None) for r in G]
            print(g, out, flush=True)

"""step5.py FILE.g6 [MAXDEC]: run the construction of re-tight Theorem 3.1 literally and check the result.

For every graph (any connectivity), every root r of degree n - 2 satisfying (**), and every Lovasz
decomposition D of B - r (up to MAXDEC per root, default all), with EVERY orientation allowed by
the theorem (d(b_i) <= d(a_i), all tie-breaks):
  * build Gamma (P_i ~ b_j iff b_j not on P_i), take a maximum matching (networkx Hopcroft-Karp),
    drop matched pairs until 1 or 2 paths are unmatched (Step 5);
  * form b_i P_i a_i r b_j (matched), b_i P_i a_i r (unmatched), b r / b r b' (unmatched trivial
    ends);
  * check from scratch: every piece is a path of B, the pieces partition E(B), there are exactly
    k pieces, and exactly two ends lie at r.
Any failure is printed.  Uses ham_frac.lovasz_decomps for the enumeration.
"""
import itertools
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, __import__("os").path.dirname(__file__))
from g6 import parse_g6  # noqa: E402
from ham_frac import lovasz_decomps  # noqa: E402
from recount_conditions import star2  # noqa: E402


def run(n, adj, r, D):
    k = n // 2
    deg = [len(a) for a in adj]
    m = len(D)
    assert m == k - 1
    choices = []
    for P in D:
        a, b = P[0], P[-1]
        opts = []
        if deg[b] <= deg[a]:
            opts.append(list(P))  # attachment a = P[0], trivial b = P[-1]: P oriented a..b
        if deg[a] <= deg[b]:
            opts.append(list(reversed(P)))
        choices.append(opts)
    bad = 0
    for orient in itertools.product(*choices):
        # orient[i] runs from a_i to b_i
        A = [P[0] for P in orient]
        Bt = [P[-1] for P in orient]
        G = nx.Graph()
        G.add_nodes_from(("P", i) for i in range(m))
        G.add_nodes_from(("b", j) for j in range(m))
        for i in range(m):
            for j in range(m):
                if Bt[j] not in orient[i]:
                    G.add_edge(("P", i), ("b", j))
        M = nx.bipartite.hopcroft_karp_matching(G, top_nodes=[("P", i) for i in range(m)])
        sig = {i: M[("P", i)][1] for i in range(m) if ("P", i) in M}
        if len(sig) < k - 3:
            return "HALL-FAIL"
        while m - len(sig) < 1:
            sig.pop(next(iter(sig)))
        assert 1 <= m - len(sig) <= 2
        paths = []
        for i in range(m):
            seq = list(reversed(orient[i])) + [r]  # b_i ... a_i r
            if i in sig:
                seq.append(Bt[sig[i]])
            paths.append(seq)
        un = [Bt[j] for j in range(m) if j not in sig.values()]
        assert len(un) == m - len(sig)
        paths.append([un[0], r] if len(un) == 1 else [un[0], r, un[1]])
        E = set()
        ends_r = 0
        for P in paths:
            if len(set(P)) != len(P) or len(P) < 2:
                bad += 1
                break
            for u, v in zip(P, P[1:]):
                if v not in adj[u] or frozenset((u, v)) in E:
                    bad += 1
                E.add(frozenset((u, v)))
            ends_r += (P[0] == r) + (P[-1] == r)
        if len(E) != sum(deg) // 2 or len(paths) != k or ends_r != 2:
            bad += 1
    return "BAD" if bad else "OK"


def main():
    maxdec = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    c = Counter()
    for line in open(sys.argv[1]):
        g = line.split()[0]
        n, adj = parse_g6(g)
        for r in range(n):
            if len(adj[r]) != n - 2 or not star2(n, adj, r):
                continue
            c["roots"] += 1
            for t, D in enumerate(lovasz_decomps(n, adj, r)):
                if maxdec and t >= maxdec:
                    c["capped roots"] += 1
                    break
                res = run(n, adj, r, D)
                c[res] += 1
                if res != "OK":
                    print(res, g, r, D)
    print(sys.argv[1], dict(c))


if __name__ == "__main__":
    main()

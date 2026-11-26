"""EMC stress test on cones: B = K1 v H, |B| = n even.

The apex has degree n-1, so p(B) >= n/2: every such cone is critical (given
Gallai).  Even vertices of B = odd-degree vertices of H.  For each random H we
compute all realisable half-sets with the circuit solver and check that they
are the bases of a loopless matroid (basis exchange).
"""
import itertools
import random
import sys
import networkx as nx
from pathnum2 import decompose


def realisable(B, S, k):
    exact = {}
    for v in B:
        d = B.degree(v)
        exact[v] = 1 if d % 2 else (2 if v in S else 0)
    st, P = decompose(B, k, exact_ends=exact, time_limit=300, workers=2)
    return P is not None, st


if __name__ == "__main__":
    n = int(sys.argv[1]); trials = int(sys.argv[2]); seed = int(sys.argv[3])
    rng = random.Random(seed)
    for t in range(trials):
        m = rng.randint(n - 1, 2 * n)
        H = nx.gnm_random_graph(n - 1, m, seed=rng.randrange(10**9))
        B = nx.Graph(H)
        B.add_edges_from((n - 1, v) for v in range(n - 1))
        E = [v for v in B if B.degree(v) % 2 == 0]
        if len(E) < 4:
            continue
        k = n // 2
        good, unk = [], []
        for S in itertools.combinations(E, len(E) // 2):
            ok, st = realisable(B, set(S), k)
            if ok:
                good.append(frozenset(S))
            elif st != "INFEASIBLE":
                unk.append(S)
        Bs = set(good)
        exch = all(any(((X - {x}) | {y}) in Bs for y in Y - X) for X in Bs for Y in Bs for x in X - Y)
        loops = [v for v in E if not any(v in S for S in Bs)]
        g6 = nx.to_graph6_bytes(B, header=False).decode().strip()
        print(f"cone {g6} e={len(E)} bases={len(good)}/{len(list(itertools.combinations(E, len(E)//2)))} "
              f"exchange={exch} loops={loops} undecided={len(unk)}", flush=True)

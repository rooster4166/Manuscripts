"""Targeted test of L_N for PERFECT matchings (every vertex paired), the Eulerian case.

F: random graph with all degrees odd on n vertices; N: a random perfect matching of non-edges of F
(any distance >= 2); random orientation.  L_N asks for a Lovasz decomposition of F in which the path
ending at each tail avoids its head (query C with single-edge routes).  Equivalently, G = F + N is a
graph with all degrees even and a perfect matching, and the orientation is realisable with every
matching edge terminal.  Also records the distance profile of the pairs.

Usage: python3 ln_perfect.py trials budget [nmin nmax]
"""
import random
import sys

import networkx as nx

import rd_lib as L
from lovasz_matching import make_all_odd


def random_pm_nonedges(F, rng, tries=100):
    V = list(F)
    for _ in range(tries):
        rng.shuffle(V)
        used, N = set(), []
        ok = True
        for u in V:
            if u in used:
                continue
            cand = [w for w in V if w not in used and w != u and not F.has_edge(u, w)]
            if not cand:
                ok = False
                break
            w = rng.choice(cand)
            N.append((u, w) if rng.random() < 0.5 else (w, u))
            used |= {u, w}
        if ok and 2 * len(N) == len(V):
            return N
    return None


def main():
    trials, L.BUDGET, L.FINAL = int(sys.argv[1]), int(sys.argv[2]), False
    nmin = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    nmax = int(sys.argv[4]) if len(sys.argv) > 4 else 20
    rng = random.Random(123)
    st = {}
    for it in range(trials):
        n = rng.choice([x for x in range(nmin, nmax + 1, 2)])
        F = nx.gnp_random_graph(n, rng.uniform(0.12, 0.5), seed=rng.randrange(10 ** 9))
        if not make_all_odd(F, rng) or F.number_of_edges() + n // 2 > 128:
            continue
        N = random_pm_nonedges(F, rng)
        if N is None:
            continue
        d = dict(nx.all_pairs_shortest_path_length(F))
        close = sum(1 for c, a in N if d[c].get(a, 99) == 2)
        G = nx.Graph(F)
        G.add_edges_from(N)
        r = L.route_respecting(G, [[c, a] for c, a in N], [a for c, a in N])
        k = n
        st.setdefault(k, [0, 0, 0, 0])
        st[k][0] += 1
        st[k][3] += close > 0
        if r is None:
            st[k][2] += 1
        elif not r:
            st[k][1] += 1
            print("FAIL", n, sorted(F.edges()), N, flush=True)
    print("n -> failures/total (undecided) [instances with a distance-2 pair]:",
          {k: f"{v[1]}/{v[0]} ({v[2]}) [{v[3]}]" for k, v in sorted(st.items())})


if __name__ == "__main__":
    main()

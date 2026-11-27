"""L_N on regular Eulerian graphs: G random 2k-regular with a perfect matching N, F = G - N is
(2k-1)-regular; random orientations of N.  L_N asks for a Lovasz decomposition of F in which the
path at each tail avoids its head (equivalently: the orientation is realisable in G with every
N-edge terminal at its head).  Usage: python3 ln_regular.py trials budget k nmin nmax"""
import random
import sys

import networkx as nx

import rd_lib as L


def main():
    trials, L.BUDGET, L.FINAL = int(sys.argv[1]), int(sys.argv[2]), False
    k, nmin, nmax = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    rng = random.Random(4000 + k)
    st = {}
    for it in range(trials):
        n = rng.choice(list(range(nmin, nmax + 1, 2)))
        if n * 2 * k // 2 > 128:
            continue
        G = nx.random_regular_graph(2 * k, n, seed=rng.randrange(10 ** 9))
        if not nx.is_connected(G):
            continue
        N = nx.max_weight_matching(nx.Graph((u, v, {"weight": rng.random()}) for u, v in G.edges()),
                                   maxcardinality=True)
        if 2 * len(N) != n:
            continue
        N = [(u, v) if rng.random() < 0.5 else (v, u) for u, v in N]
        d = dict(nx.all_pairs_shortest_path_length(nx.Graph([e for e in G.edges()
                                                             if frozenset(e) not in {frozenset(x) for x in N}])))
        close = sum(1 for c, a in N if d[c].get(a, 99) == 2)
        r = L.route_respecting(G, [[c, a] for c, a in N], [a for c, a in N])
        s = st.setdefault(n, [0, 0, 0])
        s[0] += 1
        if r is None:
            s[2] += 1
        elif not r:
            s[1] += 1
            print("FAIL", n, sorted(G.edges()), N, flush=True)
    print(f"2k={2*k}: n -> [total, failures, undecided]", dict(sorted(st.items())))


if __name__ == "__main__":
    main()

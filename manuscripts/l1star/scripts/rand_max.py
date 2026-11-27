"""Random tests of the local form of L1* (l1star session).

For a graph G with at most one vertex g of positive even degree and an odd vertex c, let
Amax = (vertices of positive degree) - N[c] - N(g).  Test: some Lovász decomposition has its
path Q_c disjoint from Amax, i.e. V(Q_c) is contained in N[c] u N(g).  Every instance of L1*
(|A| <= 2) is implied.

Graphs: G(n,p), parities repaired by toggling edges between pairs of even vertices, so that
odd n gives exactly one even vertex and even n gives none (connected, no isolated vertex).
Queries use a node budget; undecided answers (2) are counted separately.

usage: python3 rand_max.py N_GRAPHS SEED BUDGET n1 [n2 ...]
"""
import sys, random, subprocess, os, collections
import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))


class Oracle:
    def __init__(self, budget):
        self.p = subprocess.Popen([os.path.join(HERE, "l1s"), "ed", str(budget)],
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

    def q(self, G, c, mask):
        E = list(G.edges())
        self.p.stdin.write(f"{G.number_of_nodes()} {len(E)} " + " ".join(f"{u} {v}" for u, v in E)
                           + f" {c} {mask}\n")
        self.p.stdin.flush()
        return int(self.p.stdout.readline())


def random_graph(n, p, rng):
    for _ in range(1000):
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(1 << 30))
        if not nx.is_connected(G):
            continue
        ev = [v for v in G if G.degree(v) % 2 == 0]
        if len(ev) % 2:
            g = rng.choice(ev)
            ev = [v for v in ev if v != g]
        rng.shuffle(ev)
        for i in range(0, len(ev), 2):
            a, b = ev[i], ev[i + 1]
            if G.has_edge(a, b):
                G.remove_edge(a, b)
            else:
                G.add_edge(a, b)
        if not nx.is_connected(G) or G.number_of_edges() > 128:
            continue
        evs = [v for v in G if G.degree(v) % 2 == 0]
        if len(evs) > 1:
            continue
        return G, (evs[0] if evs else None)
    return None


def main():
    N, seed, budget = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    ns = [int(a) for a in sys.argv[4:]]
    rng = random.Random(seed)
    O = Oracle(budget)
    C = collections.Counter()
    for it in range(N):
        n = rng.choice(ns)
        r = random_graph(n, rng.uniform(0.15, 0.6), rng)
        if r is None:
            continue
        G, g = r
        C[f"graphs n={n}"] += 1
        Ng = set(G[g]) if g is not None else set()
        for c in G:
            if G.degree(c) % 2 == 0:
                continue
            bad = set(G[c]) | {c} | Ng
            A = [v for v in G if v not in bad]
            mask = sum(1 << v for v in A)
            res = O.q(G, c, mask)
            C["tests"] += 1
            if res == 0:
                C["FAIL"] += 1
                print("FAIL", nx.to_graph6_bytes(G, header=False).decode().strip(), g, c, A, flush=True)
            elif res == 2:
                C["undecided"] += 1
        if (it + 1) % 200 == 0:
            print("PARTIAL", it + 1, dict(C), flush=True)
    print("SUMMARY", dict(sorted(C.items())), flush=True)


if __name__ == "__main__":
    main()

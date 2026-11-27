"""Random tests of PEE, EE, the away-edge conjectures and L1* (prescribed-end session).

Graphs: connected, odd order n, exactly one vertex z of positive even degree, no isolated
vertices (G(n,p) with parities repaired by toggling edges between pairs of wrong-parity vertices).

For each graph:
  * EE: every u in N(z), d(u) >= 3: is uz terminal at u?
  * away: a sample of ordered edges (x, y), y != z, d(x) >= 3: is xy terminal at x?  On a failure,
    the reverse (terminal at y), y ~ z (P1) and dist(x, z) >= 3 (P3) are recorded.
  * L1*: a sample of pairs (c, a), c odd, a not in N[c] u N(z) (a = z allowed): Q_c avoids a.
  * triangle lemma: for u in N(z) and w in N(u) & N(z): K - {uz, uw, zw} has a Lovasz
    decomposition whose path at w avoids u and z.
Queries use a node budget; undecided answers (2) are counted separately.

usage: python3 rand_test.py N_GRAPHS SEED BUDGET n1 [n2 ...]
"""
import sys, random, subprocess, os, collections
import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))


class Oracle:
    def __init__(self, budget):
        self.p = subprocess.Popen([os.path.join(HERE, "pee2"), "edq", str(budget)],
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

    def q(self, G, T, a, b):
        E = list(G.edges())
        self.p.stdin.write(f"{G.number_of_nodes()} {len(E)} " + " ".join(f"{u} {v}" for u, v in E) + f" {T} {a} {b}\n")
        self.p.stdin.flush()
        return int(self.p.stdout.readline())


def random_one_even(n, p, rng):
    for _ in range(1000):
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(1 << 30))
        if not nx.is_connected(G):
            continue
        ev = [v for v in G if G.degree(v) % 2 == 0]
        z = rng.choice(ev)
        rest = [v for v in ev if v != z]
        rng.shuffle(rest)
        for i in range(0, len(rest), 2):
            a, b = rest[i], rest[i + 1]
            if G.has_edge(a, b):
                G.remove_edge(a, b)
            else:
                G.add_edge(a, b)
        if not nx.is_connected(G) or G.degree(z) == 0 or G.degree(z) % 2:
            continue
        if any(G.degree(v) % 2 == 0 for v in G if v != z):
            continue
        return G, z
    return None


def main():
    N, seed, budget = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    ns = [int(a) for a in sys.argv[4:]]
    rng = random.Random(seed)
    O = Oracle(budget)
    C = collections.Counter()
    for it in range(N):
        n = rng.choice(ns)
        r = random_one_even(n, rng.uniform(0.15, 0.5), rng)
        if r is None:
            continue
        G, z = r
        C["graphs"] += 1
        Nz = set(G[z])
        # EE
        for u in sorted(Nz):
            if G.degree(u) < 3:
                continue
            T = len(Nz & set(G[u]))
            res = O.q(G, 0, u, z)
            key = "EE|T|>=2" if T >= 2 else "EE|T|<=1"
            C[key + ":tests"] += 1
            if res == 0:
                C[key + ":FAIL"] += 1
                print("EEFAIL", nx.to_graph6_bytes(G, header=False).decode().strip(), z, u, flush=True)
            elif res == 2:
                C[key + ":undecided"] += 1
        # away edges (sample)
        arcs = [(x, y) for x in G for y in G[x] if x != z and y != z and G.degree(x) >= 3]
        rng.shuffle(arcs)
        dist = nx.single_source_shortest_path_length(G, z)
        for x, y in arcs[:12]:
            res = O.q(G, 0, x, y)
            C["away:tests"] += 1
            if res == 2:
                C["away:undecided"] += 1
                continue
            if res == 1:
                continue
            C["away:fail"] += 1
            if y in Nz:
                C["away:fail_with_y~z(P1 violated)"] += 1
                print("P1FAIL", nx.to_graph6_bytes(G, header=False).decode().strip(), z, x, y, flush=True)
            if dist[x] >= 3:
                C["away:fail_with_dist(x,z)>=3(P3 violated)"] += 1
                print("P3FAIL", nx.to_graph6_bytes(G, header=False).decode().strip(), z, x, y, flush=True)
            rr = O.q(G, 0, y, x) if G.degree(y) >= 3 else 1
            if rr == 0:
                C["away:both_ends_fail(P2 violated)"] += 1
                print("P2FAIL", nx.to_graph6_bytes(G, header=False).decode().strip(), z, x, y, flush=True)
            elif rr == 2:
                C["away:reverse_undecided"] += 1
        # L1* (sample)
        pairs = []
        for c in G:
            if c == z:
                continue
            bad = set(G[c]) | {c} | Nz
            for a in G:
                if a not in bad:
                    pairs.append((c, a))
        rng.shuffle(pairs)
        for c, a in pairs[:8]:
            res = O.q(G, 1, c, 1 << a)
            k = "L1*(a=z)" if a == z else "L1*(a!=z)"
            C[k + ":tests"] += 1
            if res == 0:
                C[k + ":FAIL"] += 1
                print("L1SFAIL", nx.to_graph6_bytes(G, header=False).decode().strip(), z, c, a, flush=True)
            elif res == 2:
                C[k + ":undecided"] += 1
        # triangle lemma
        for u in sorted(Nz):
            for w in sorted(Nz & set(G[u])):
                H = G.copy()
                H.remove_edges_from([(u, z), (u, w), (z, w)])
                res = O.q(H, 1, w, (1 << u) | (1 << z))
                C["tri:tests"] += 1
                if res == 0:
                    C["tri:FAIL"] += 1
                    print("TRIFAIL", nx.to_graph6_bytes(G, header=False).decode().strip(), z, u, w, flush=True)
                elif res == 2:
                    C["tri:undecided"] += 1
        if (it + 1) % 50 == 0:
            print("PROGRESS", it + 1, dict(C), flush=True)
    print("FINAL", dict(C), flush=True)


if __name__ == "__main__":
    main()

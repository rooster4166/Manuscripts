"""Targeted test of the residual configuration in the L-infinity induction (connections V.4c).
K = F' + leaf l at c, with exactly one positive-even vertex z, d(c, z) = 3, every neighbour of z at
distance exactly 2 from c, and deg z >= 4 or z on a triangle.  Question (GL): is there a Lovasz
decomposition whose path through l stays inside {l} + N[c]?
Usage: python3 residual_test.py trials budget"""
import random
import sys

import networkx as nx

import rd_lib as L


def build(rng):
    # layers: c | N(c) | L2 | z (+ optional far stuff)
    d1 = rng.choice([1, 3, 5])
    n2 = rng.randint(3, 6)
    G = nx.Graph()
    c, l = 0, 1
    N1 = list(range(2, 2 + d1))
    L2 = list(range(2 + d1, 2 + d1 + n2))
    z = 2 + d1 + n2
    G.add_edge(c, l)
    for w in N1:
        G.add_edge(c, w)
    for u in L2:  # every L2 vertex gets >= 1 neighbour in N1
        G.add_edge(u, rng.choice(N1))
    for _ in range(rng.randint(0, 6)):
        a, b = rng.sample(N1 + L2, 2)
        G.add_edge(a, b)
    k = rng.choice([4, 4, 6]) if n2 >= 4 else 2
    k = min(k, n2 - (n2 % 2 == 1 and k > n2))
    nbrs = rng.sample(L2, min(k, n2))
    for u in nbrs:
        G.add_edge(z, u)
    # extra far vertices to fix parities
    nxt = z + 1
    for _ in range(rng.randint(0, 3)):
        G.add_edge(nxt, rng.choice(L2 + [z]))
        nxt += 1
    return G, c, l, z


def fix(G, rng, c, l, z):
    """Make every vertex odd except z (even, positive) and c (odd); never touch the leaf l or the
    distances: only toggle edges between non-c, non-l vertices at distance >= 2 from c."""
    for _ in range(300):
        dist = nx.single_source_shortest_path_length(G, c)
        bad = [v for v in G if v not in (l,) and (G.degree(v) % 2 == 0) != (v == z)]
        if not bad:
            return True
        cand = [v for v in bad if v != c]
        if len(cand) < 2:
            # attach a new far leaf to fix a single bad vertex
            if cand:
                v = cand[0]
                G.add_edge(v, max(G) + 1)
                continue
            return False
        x, y = rng.sample(cand, 2)
        if G.has_edge(x, y):
            G.remove_edge(x, y)
        else:
            G.add_edge(x, y)
    return False


def residual(G, c, l, z):
    dist = nx.single_source_shortest_path_length(G, c)
    if dist.get(z) != 3 or G.degree(c) % 2 == 0 or G.degree(l) != 1:
        return False
    if any(dist.get(u) != 2 for u in G[z]):
        return False
    ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    if ev != [z]:
        return False
    tri = any(G.has_edge(a, b) for a in G[z] for b in G[z] if a < b)
    return G.degree(z) >= 4 or tri


def gen(rng):
    n = rng.randint(9, 14)
    G = nx.gnp_random_graph(n, rng.uniform(0.12, 0.35), seed=rng.randrange(10 ** 9))
    c, z = rng.sample(range(n), 2)
    for _ in range(200):
        bad = [v for v in G if (G.degree(v) % 2 == 0) != (v in (c, z))]
        if not bad:
            break
        if len(bad) == 1:
            return None
        x, y = rng.sample(bad, 2)
        if G.has_edge(x, y):
            G.remove_edge(x, y)
        else:
            G.add_edge(x, y)
    else:
        return None
    if G.degree(c) == 0 or G.degree(z) == 0:
        return None
    l = n
    G.add_edge(c, l)
    return G, c, l, z


def main():
    trials, L.BUDGET, L.FINAL = int(sys.argv[1]), int(sys.argv[2]), False
    rng = random.Random(9090)
    tot = bad = und = 0
    for it in range(trials):
        r0 = gen(rng)
        if r0 is None:
            continue
        H, c, l, z = r0
        if not residual(H, c, l, z) or H.number_of_edges() > 100:
            continue
        b = [H.degree(v) % 2 for v in range(H.number_of_nodes())]
        B = {l, c} | set(H[c])
        Y = set(H) - B
        r = L.avoid(H, b, {l: Y})
        tot += 1
        if r is None:
            und += 1
        elif not r:
            bad += 1
            print("FAIL", sorted(H.edges()), "c", c, "l", l, "z", z, flush=True)
    print(f"residual GL: total {tot} failures {bad} undecided {und}")


if __name__ == "__main__":
    main()

"""How often does the far-apart form of the chained walk theorem apply at d(z) = 6?

Random 3-connected J with degrees (6, 3/5, ...), z the only even vertex.  Hypothesis (Cor. 8.4):
the six neighbours of z are pairwise at distance >= 3 in J - z; then the base hypothesis of
Theorem 8.2 holds for every admissible chain (sparse separation), so STL(J, z, r) holds for each
r that is a long end y_i of a labelled pairing with an admissible chain.  An admissible chain is
searched for as: P2 a shortest constrained path y3 -> x2, then P1 a shortest constrained path
y2 -> x1 edge-disjoint from P2 (a sufficient search, so the counts are lower bounds).

usage: d6_reach.py COUNT SEED n1 n2 ...
"""
import sys, random, itertools
from collections import deque
import networkx as nx


def pairings(xs):
    if not xs:
        yield []
        return
    a = xs[0]
    for i in range(1, len(xs)):
        for p in pairings(xs[1:i] + xs[i + 1:]):
            yield [(a, xs[i])] + p


def bfs_path(H, s, t, allowed, banned_edges=frozenset()):
    """shortest path s -> t whose vertices other than t satisfy allowed(v); None if none."""
    prev = {s: None}
    q = deque([s])
    while q:
        v = q.popleft()
        if v == t:
            path = [t]
            while prev[path[-1]] is not None:
                path.append(prev[path[-1]])
            return path[::-1]
        for w in H[v]:
            if w in prev or frozenset((v, w)) in banned_edges:
                continue
            if w != t and not allowed(w):
                continue
            prev[w] = v
            q.append(w)
    return None


def chain(H, X, Y):
    """admissible chain for labels x_i = X[i], y_i = Y[i] in H = J - z (F-edges not in H)."""
    x1, x2, x3 = X
    y1, y2, y3 = Y
    N2, N3 = set(H[x2]), set(H[x3])
    if y2 in N3:
        return False
    P2 = bfs_path(H, y3, x2, lambda w: w not in (x1, y1, y2, x3, x2) and w not in N3)
    if P2 is None:
        return False
    used = {frozenset(e) for e in zip(P2, P2[1:])}
    # P1 avoids N_G(x3), which contains y3 through the F-edge x3y3 (as in the Lean AdmChain)
    P1 = bfs_path(H, y2, x1, lambda w: w not in (y1, x2, x3, x1, y3) and w not in N2 and w not in N3,
                  used)
    return P1 is not None


def main():
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    for n in map(int, sys.argv[3:]):
        made = far = covered = 0
        while made < count:
            degs = [6] + [rng.choice((3, 3, 3, 5)) for _ in range(n - 1)]
            if sum(degs) % 2:
                continue
            G = nx.Graph(nx.configuration_model(degs, seed=rng.randrange(1 << 30)))
            G.remove_edges_from(nx.selfloop_edges(G))
            if [G.degree(v) for v in range(n)] != degs or nx.node_connectivity(G) < 3:
                continue
            made += 1
            Nz = sorted(G[0])
            H = G.copy()
            H.remove_node(0)
            dist = {u: nx.single_source_shortest_path_length(H, u, cutoff=2) for u in Nz}
            if any(v in dist[u] for u, v in itertools.combinations(Nz, 2)):
                continue
            far += 1
            cov = set()
            for F in pairings(Nz):
                for perm in itertools.permutations(range(3)):
                    for o in range(8):
                        X = [F[perm[i]][(o >> i) & 1] for i in range(3)]
                        Y = [F[perm[i]][1 - ((o >> i) & 1)] for i in range(3)]
                        if set(Y) <= cov:
                            continue
                        if chain(H, X, Y):
                            cov |= set(Y)
                if len(cov) == 6:
                    break
            covered += len(cov) == 6
        print(f"n={n} graphs={made} far={far} far_and_all_r_covered={covered}", flush=True)


if __name__ == '__main__':
    main()

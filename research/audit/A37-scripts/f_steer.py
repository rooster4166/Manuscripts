"""f_steer.py (audit A37, item 3f): an implementation of the Lean inductive
`Steer2 X K a b` (TRNSteer.lean) written directly from its three constructors, on
K = apex G {y} (a leaf L = 'L' at y) and X = {L, x}:
  fin  : K.Adj a u, u not in X, u != b, and every K-neighbour of u is a          -> Steer2 X K a b
  step : K.Adj a u, u not in X, u != b, not (K - au).Adj u b, Steer2 X (K - au) u b -> Steer2 X K a b
  swap : Steer2 X K b a                                                            -> Steer2 X K a b
As a least fixed point, Steer2 K a b <=> Move(K,a,b) or Move(K,b,a), where Move uses only
graphs with fewer edges (well-founded).  Compared with dz4_cover.steer2 (the session's port of
trn/scripts/steer2.cpp) on every data choice (w, y, x) of the order-8 d(z) = 4 instances and of a
seeded sample of order-10 triangle instances; also recounts the order-8 FAR / STEER split.
usage: python3 f_steer.py N10 SEED
"""
import gzip
import random
import sys
from collections import Counter

HERE = __file__.rsplit("/", 1)[0]
sys.path.insert(0, HERE)
sys.path.insert(1, "/home/user/Manuscripts/manuscripts/test2/scripts")
from a37lib import adjacency, g6_decode  # noqa: E402
import dz4_cover  # noqa: E402  (the session's port, compared against)

D = "/home/user/Manuscripts/manuscripts/test2/data/"


class Cap(Exception):
    pass


def lean_steer2(Gedges, g, y, x, cap=2_000_000):
    """Steer2 (leafX x) (apex G {y}) (some g) (some y), decided from the constructors."""
    K0 = frozenset(frozenset(e) for e in Gedges) | {frozenset(("L", y))}
    X = {"L", x}
    memo = {}
    cnt = [0]

    def nbrs(K, v):
        return [next(iter(e - {v})) for e in K if v in e]

    def move(K, a, b):
        for u in nbrs(K, a):
            if u in X or u == b:
                continue
            if all(w == a for w in nbrs(K, u)):          # fin
                return True
            K2 = K - {frozenset((a, u))}
            if frozenset((u, b)) in K2:                   # step needs: not (K - au).Adj u b
                continue
            if steer(K2, u, b):
                return True
        return False

    def steer(K, a, b):
        key = (K, frozenset((a, b)))                      # swap makes the pair unordered
        if key in memo:
            return memo[key]
        cnt[0] += 1
        if cnt[0] > cap:
            raise Cap
        res = move(K, a, b) or move(K, b, a)
        memo[key] = res
        return res

    try:
        return steer(K0, g, y)
    except Cap:
        return None


def choices(n, E, z, r):
    A = adjacency(n, E)
    U = [u for u in sorted(A[z]) if u != r]
    out = []
    for w in U:
        a, b = [u for u in U if u != w]
        if b in A[a]:
            out.append((w, a, b))
    return out


def compare(g6, z, r, st, settle_order=True):
    n, E = g6_decode(g6)
    data = choices(n, E, z, r)
    if not data:
        return "nodata"
    how = None
    for w, a, b in data:
        G = {e for e in E if z not in e} - {frozenset((a, b))}
        A = adjacency(n, G)
        far = not (A[a] & A[b])
        adj = [0] * n
        for e in G:
            u, v = tuple(e)
            adj[u] |= 1 << v
            adj[v] |= 1 << u
        for y, x in ((b, a), (a, b)):
            mine = lean_steer2(G, w, y, x)
            theirs = dz4_cover.steer2(adj, w, y, x, 2_000_000)
            st[("agree", mine == theirs)] += 1
            if mine != theirs:
                print("DISAGREE", g6, z, r, w, y, x, mine, theirs, flush=True)
            if how is None and far:
                how = "FAR"
            if how is None and mine:
                how = "STEER"
    return how or "not covered"


def main():
    N10, seed = int(sys.argv[1]), int(sys.argv[2])
    st = Counter()
    c8 = Counter()
    for line in open(D + "t2_order6_8.txt"):
        g6, z, r, dz = line.split()[:4]
        if int(dz) != 4 or g6_decode(g6)[0] != 8:
            continue
        c8[compare(g6, int(z), int(r), st)] += 1
    print("order 8, d(z)=4:", dict(c8))
    with gzip.open(D + "t2_order10_fields.txt.gz", "rt") as fh:
        tri = []
        for line in fh:
            g6, z, r, dz = line.split()[:4]
            if int(dz) != 4:
                continue
            n, E = g6_decode(g6)
            A = adjacency(n, E)
            U = [u for u in A[int(z)] if u != int(r)]
            if all(U[j] in A[U[i]] for i in range(3) for j in range(i + 1, 3)):
                tri.append((g6, int(z), int(r)))
    rng = random.Random(seed)
    c10 = Counter()
    for g6, z, r in rng.sample(tri, N10):
        c10[compare(g6, z, r, st)] += 1
    print("order 10 triangle sample:", dict(c10), "of", N10, "(population", len(tri), ")")
    print(dict(st))


if __name__ == "__main__":
    main()

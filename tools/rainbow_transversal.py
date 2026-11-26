"""Rainbow transversals of Hamiltonian decompositions (endpoint-structure §7, the flower move).

A system of k edge-disjoint Hamiltonian cycles C_1..C_k on N vertices has a *transversal through s*
if some path through s has exactly one edge from each C_i. The flower move needs one for the
k = m - 1 Hamiltonian cycles left at Fan's equality in CP(m) = K_{2m} minus a perfect matching.
It is proved for k <= 4 (Lean `rainbowTransversal_three`, `rainbowTransversal_four`).

For CP(m) this script tests:
  * random Hamiltonian decompositions (randomised DFS, then the last cycle must close up);
  * the Walecki-type decomposition of K_{2m} minus a perfect matching.
For every vertex s it asks for a transversal starting at s, which is stronger than one through s,
by exhaustive search. It also reports how often a random greedy choice succeeds without
backtracking.

Usage: python3 tools/rainbow_transversal.py MMAX SAMPLES [seed]
"""
import random
import sys

sys.setrecursionlimit(10000)


def ham_cycle(n, adj, rng, tries=60):
    for _ in range(tries):
        start = rng.randrange(n)
        path, seen = [start], {start}

        def dfs():
            if len(path) == n:
                return start in adj[path[-1]]
            cand = list(adj[path[-1]] - seen)
            rng.shuffle(cand)
            cand.sort(key=lambda x: len(adj[x] - seen))
            for x in cand[:3]:
                path.append(x); seen.add(x)
                if dfs():
                    return True
                path.pop(); seen.discard(x)
            return False
        if dfs():
            return path
    return None


def random_decomposition(m, rng):
    n, k = 2 * m, m - 1
    adj0 = {v: set(range(n)) - {v, v ^ 1} for v in range(n)}  # antipode of v is v ^ 1
    for _ in range(300):
        adj = {v: set(a) for v, a in adj0.items()}
        cyc = []
        for i in range(k):
            c = ham_cycle(n, adj, rng, 5 if i == k - 1 else 60)
            if c is None:
                break
            cyc.append(c)
            for a, b in zip(c, c[1:] + c[:1]):
                adj[a].discard(b); adj[b].discard(a)
        if len(cyc) == k and all(not adj[v] for v in adj):
            return n, cyc
    return None


def walecki(m):
    n, q, inf = 2 * m, 2 * m - 1, 2 * m - 1
    cyc = []
    for i in range(m - 1):
        seq = [i]
        for j in range(1, m):
            seq.append((i + j) % q)
            seq.append((i - j) % q)
        cyc.append([inf] + seq[:q])
    return n, cyc


def colour_nbrs(n, cyc):
    nb = {v: {} for v in range(n)}
    for i, c in enumerate(cyc):
        for a, b in zip(c, c[1:] + c[:1]):
            nb[a].setdefault(i, []).append(b)
            nb[b].setdefault(i, []).append(a)
    return nb


def transversal_from(nb, k, s):
    def grow(p, used):
        if len(p) - 1 == k:
            return True
        v = p[-1]
        for i in range(k):
            if i in used:
                continue
            for u in nb[v][i]:
                if u not in p:
                    p.append(u)
                    if grow(p, used | {i}):
                        return True
                    p.pop()
        return False
    return grow([s], frozenset())


def greedy(nb, k, s, rng):
    p, used = [s], set()
    while len(p) - 1 < k:
        opts = [(i, u) for i in range(k) if i not in used for u in nb[p[-1]][i] if u not in p]
        if not opts:
            return False
        i, u = rng.choice(opts)
        p.append(u); used.add(i)
    return True


def main():
    mmax = int(sys.argv[1]); samples = int(sys.argv[2])
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    for m in range(4, mmax + 1):
        k = m - 1
        n, cyc = walecki(m)
        nb = colour_nbrs(n, cyc)
        wfail = [s for s in range(n) if not transversal_from(nb, k, s)]
        got = fails = gt = gs = 0
        for _ in range(samples):
            r = random_decomposition(m, rng)
            if r is None:
                continue
            n, cyc = r
            got += 1
            nb = colour_nbrs(n, cyc)
            for s in range(n):
                fails += not transversal_from(nb, k, s)
                for _ in range(10):
                    gt += 1; gs += greedy(nb, k, s, rng)
        print(f"m={m}: Walecki failures {wfail}; random decompositions {got}, "
              f"(decomposition, vertex) pairs without a transversal from s: {fails}; "
              f"random greedy succeeds {gs}/{gt}", flush=True)


if __name__ == "__main__":
    main()

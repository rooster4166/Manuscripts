"""Least held-set size at which the Fan game wins each root (audit A12; solver game.py).

For each graph (graph6 per line): for k = kmin..kmax, enumerate held sets of size k that admit a
seed, one per orbit of Aut(G) (if F wins the roots M, then phi(F) wins phi(M)), evaluate the exact
set of winning roots, and close it under Aut(G). Prints, per graph, the least k for every root
(None if no win up to kmax) and the maximum over the roots.
Options: nonp (no path insertion: the original game), split (the split rule sum b <= n - 2).
Usage: nice python3 sweep.py FILE kmin kmax [nonp] [split] [skipwon]
  skipwon: stop as soon as every root is won (default: yes); a graph is reported LOSE if some root
  has no win up to kmax."""
import sys, time
from itertools import combinations
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
import game


def run(g6, kmin, kmax, newpath=True, split=False, maxauto=5000):
    G = nx.from_graph6_bytes(g6.encode())
    n = G.number_of_nodes()
    gm = game.Game(n, list(G.edges()), newpath=newpath, split=split)
    autos = []
    for a in GraphMatcher(G, G).isomorphisms_iter():
        autos.append(tuple(a[v] for v in range(n)))
        if len(autos) > maxauto:
            break
    eperm = [[gm.eid[tuple(sorted((p[a], p[c])))] for (a, c) in gm.E] for p in autos]

    def close(mask):
        out = 0
        for p in autos:
            for v in range(n):
                if (mask >> v) & 1:
                    out |= 1 << p[v]
        return out

    least = {}
    won = 0
    for k in range(kmin, kmax + 1):
        seen = set()
        for F in combinations(range(gm.m), k):
            Fs, sd = gm.seeds(F)
            if not sd:
                continue
            if len(autos) > 1:
                key = min(tuple(sorted(p[i] for i in F)) for p in eperm)
                if key in seen:
                    continue
                seen.add(key)
                Fs, sd = gm.seeds(key)
            for kind, b0 in sd:
                won |= gm.value(Fs, b0)
            if won == gm.full:
                break
        won = close(won)
        for v in range(n):
            if (won >> v) & 1 and v not in least:
                least[v] = k
        if won == gm.full:
            break
        if len(gm.memo) > 20_000_000:
            gm.memo.clear()
    roots = {v: least.get(v) for v in range(n)}
    return roots, len(autos)


if __name__ == "__main__":
    path, kmin, kmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    opts = sys.argv[4:]
    nlose = 0; ng = 0
    for line in open(path):
        g6 = line.strip()
        if not g6:
            continue
        ng += 1
        t = time.time()
        roots, na = run(g6, kmin, kmax, newpath="nonp" not in opts, split="split" in opts)
        lose = [v for v, k in roots.items() if k is None]
        mx = None if lose else max(roots.values())
        if lose:
            nlose += 1
        if lose or "all" in opts:
            print("LOSE" if lose else "WIN", g6, "aut", na, "least", roots, "max", mx,
                  "losing roots", lose, round(time.time() - t, 1), "s", flush=True)
        elif mx is not None and mx >= kmin + 0 and "quiet" not in opts:
            pass
    print(f"{ng} graphs, {nlose} with a losing root (k <= {kmax}; opts {opts})", flush=True)

"""Variants of the rainbow-transversal question (endpoint-structure, Question 66).

  twofactor M SAMPLES : colour classes arbitrary 2-factors of CP(m) (short cycles allowed);
                        is there a transversal starting at every vertex?
  segment   M SAMPLES : segment transversals (one contiguous segment of each cycle) by a
                        no-backtracking rule, and the same rule restricted to unit segments.
  warnsdorff M SAMPLES: plain transversals by a Warnsdorff-type greedy without backtracking.
Usage: python3 tools/rainbow_variants.py MODE MMAX SAMPLES
"""
import os, random, sys
sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rainbow_transversal import random_decomposition, colour_nbrs, walecki, transversal_from
def random_two_factor(n, adj, rng, tries=200):
    # cover all vertices by vertex-disjoint cycles (length >= 3) using edges of adj
    for _ in range(tries):
        left = set(range(n)); cycles = []; ok = True
        while left:
            start = min(left, key=lambda v: (len(adj[v] & left), rng.random()))
            # random DFS for a cycle through start within 'left'
            found = None
            for _ in range(50):
                path = [start]; seen = {start}
                while True:
                    v = path[-1]
                    if len(path) >= 3 and start in adj[v] and rng.random() < 0.35:
                        found = path; break
                    cand = list((adj[v] & left) - seen)
                    if not cand:
                        if len(path) >= 3 and start in adj[v]: found = path
                        break
                    w = rng.choice(cand); path.append(w); seen.add(w)
                if found: break
            if not found: ok = False; break
            cycles.append(found); left -= set(found)
        if ok: return cycles
    return None
def decomp(m, rng):
    n, k = 2 * m, m - 1
    for _ in range(500):
        adj = {v: set(range(n)) - {v, v ^ 1} for v in range(n)}
        classes = []
        for i in range(k):
            f = random_two_factor(n, adj, rng)
            if f is None: break
            classes.append(f)
            for c in f:
                for a, b in zip(c, c[1:] + c[:1]): adj[a].discard(b); adj[b].discard(a)
        if len(classes) == k and all(not adj[v] for v in adj): return n, classes
    return None
def succmap(cyc):
    succ = {}
    for i, c in enumerate(cyc):
        n = len(c)
        for j, v in enumerate(c):
            succ[(i, v, 1)] = c[(j + 1) % n]; succ[(i, v, -1)] = c[(j - 1) % n]
    return succ
def rule(cyc, k, s, unit=False):
    succ = succmap(cyc); nb = colour_nbrs(len(cyc[0]), cyc)
    path = [s]; R = set(range(k))
    while R:
        v = path[-1]; best = None
        inpath = set(path)
        for c in R:
            for d in (1, -1):
                run = []; w = succ[(c, v, d)]
                while w not in inpath and w not in run:
                    run.append(w)
                    if unit: break
                    w = succ[(c, w, d)]
                R2 = R - {c}
                for j, wj in enumerate(run):
                    blocked = inpath | set(run[:j + 1])
                    score = sum(1 for c2 in R2 if any(u not in blocked for u in nb[wj][c2]))
                    key = (score == len(R2), score, -j)
                    if best is None or key > best[0]: best = (key, c, run[:j + 1])
        if best is None: return False
        _, c, seg = best; path += seg; R.discard(c)
    return True
def warnsdorff(nb, k, s):
    p = [s]; used = set()
    while len(p) - 1 < k:
        v = p[-1]; R = [i for i in range(k) if i not in used]
        best = None
        for c in R:
            for w in nb[v][c]:
                if w in p: continue
                R2 = [i for i in R if i != c]
                free = sum(1 for i in R2 for u in nb[w][i] if u not in p and u != w)
                key = free
                if best is None or key > best[0]: best = (key, c, w)
        if best is None: return False
        _, c, w = best; p.append(w); used.add(c)
    return True

def main():
    mode, mmax, samples = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(5)
    for m in range(4, mmax + 1):
        k = m - 1
        if mode == "twofactor":
            got = fails = 0
            for _ in range(samples):
                r = decomp(m, rng)
                if r is None:
                    continue
                n, classes = r
                got += 1
                nb = {v: {} for v in range(n)}
                for i, f in enumerate(classes):
                    for c in f:
                        for a, b in zip(c, c[1:] + c[:1]):
                            nb[a].setdefault(i, []).append(b); nb[b].setdefault(i, []).append(a)
                fails += any(not transversal_from(nb, k, s) for s in range(n))
            print(f"m={m}: 2-factorisations {got}, with a vertex starting no transversal: {fails}", flush=True)
        else:
            tot = ok = oku = 0
            for _ in range(samples):
                r = random_decomposition(m, rng)
                if r is None:
                    continue
                n, cyc = r
                nb = colour_nbrs(n, cyc)
                for s in range(n):
                    tot += 1
                    if mode == "segment":
                        ok += rule(cyc, k, s); oku += rule(cyc, k, s, unit=True)
                    else:
                        ok += warnsdorff(nb, k, s)
            extra = f", unit segments only {oku}/{tot}" if mode == "segment" else ""
            print(f"m={m}: {mode} rule succeeds {ok}/{tot}{extra}", flush=True)


if __name__ == "__main__":
    main()

"""The Fan game with oracle seeds: how far can a stronger induction hypothesis go?

This is the game of tools/fan_game.py (Lovász seed, then Fan transfers), except that the
seed on K = G - F (F nonempty) is ANY realisable simple profile of K: b = 1 on the odd vertices
of K, 2 on a realisable set S_K of even vertices of K, 0 elsewhere.  The realisable family of K
comes from the exact oracle tools/realis.c.  So a winning play shows that complete knowledge of
the realisable family of the proper subgraph G - F (the strongest hypothesis on endpoint SETS)
plus Fan moves certifies the rooted test at r.  A losing root shows that no induction
hypothesis about realisable sets of G - F, |F| <= kmax, can be turned into a certificate
for (G, r) by Fan moves.

Moves (as in fan_game.py): single transfer of ut towards u if b(t) > |Z_H(u)|; grouped
transfer at u with an adversarial donor; new one-edge path.  Win: F used up, sum b <= n,
b(r) >= 1.

With ROOTS ending in "+gen" the seed may be any realisable end profile of K with sum <= n
(not only simple profiles): the strongest hypothesis on end profiles.

Usage: python3 tools/fan_oracle.py FILE.g6 kmax [ROOTS=even|all|r1,r2,..][+gen] [workers]
"""
import os
import sys
from functools import lru_cache
from itertools import combinations
from multiprocessing import Pool

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import realis


def general_profiles(K, n):
    """All realisable end profiles b of K with sum b <= n (tools/realis.c, profile query)."""
    deg = [K.degree(v) for v in range(n)]
    out = []

    def rec(v, b, s):
        if v == n:
            if realis.profile_ok(K, b):
                out.append(tuple(b))
            return
        start = deg[v] % 2
        for x in range(start, min(deg[v], n - s) + 1, 2):
            if deg[v] % 2 == 1 and x == 0:
                continue
            b.append(x)
            rec(v + 1, b, s + x)
            b.pop()
    rec(0, [], 0)
    return out


def solve_graph(G, kmax=1, roots=None, general=False):
    G = nx.convert_node_labels_to_integers(G)
    n = G.number_of_nodes()
    E = sorted(tuple(sorted(e)) for e in G.edges())
    nbr = [0] * n
    for a, b in E:
        nbr[a] |= 1 << b
        nbr[b] |= 1 << a

    def popc(x):
        return bin(x).count("1")

    @lru_cache(maxsize=None)
    def win(rem, b, r):
        s = sum(b)
        if s > n:
            return False
        if not rem:
            return b[r] >= 1
        remmask = [0] * n
        for a, c in rem:
            remmask[a] |= 1 << c
            remmask[c] |= 1 << a
        zero = 0
        for v in range(n):
            if b[v] == 0:
                zero |= 1 << v

        def Z(u):
            return popc(nbr[u] & ~remmask[u] & zero)
        for (a, c) in rem:
            rest = rem - {(a, c)}
            for u, t in ((a, c), (c, a)):
                if b[t] > Z(u):
                    nb = list(b); nb[u] += 1; nb[t] -= 1
                    if win(rest, tuple(nb), r):
                        return True
            if s + 2 <= n:
                nb = list(b); nb[a] += 1; nb[c] += 1
                if win(rest, tuple(nb), r):
                    return True
        for u in range(n):
            cands = [t for t in range(n) if (min(u, t), max(u, t)) in rem]
            if len(cands) < 2:
                continue
            z = Z(u)
            for k in range(2, len(cands) + 1):
                for T in combinations(cands, k):
                    if sum(b[t] for t in T) <= z:
                        continue
                    ok = True
                    for t in T:
                        if b[t] == 0:
                            continue
                        e = (min(u, t), max(u, t))
                        nb = list(b); nb[u] += 1; nb[t] -= 1
                        if not win(rem - {e}, tuple(nb), r):
                            ok = False
                            break
                    if ok:
                        return True
        return False

    seeds_cache = {}

    def seeds(F):
        if F in seeds_cache:
            return seeds_cache[F]
        K = G.copy()
        K.remove_edges_from(F)
        if general:
            out = general_profiles(K, n)
            seeds_cache[F] = out
            return out
        deg = dict(K.degree())
        Ev, fam = realis.family(K)
        base = [deg[v] % 2 for v in range(n)]
        o = sum(base)
        out = []
        for S in fam:
            if o + 2 * len(S) > n:
                continue
            b = list(base)
            for v in S:
                b[v] = 2
            out.append(tuple(b))
        seeds_cache[F] = out
        return out

    deg = dict(G.degree())
    if roots is None:
        roots = range(n)
    elif roots == "even":
        roots = [v for v in range(n) if deg[v] % 2 == 0]
    result = {}
    for r in roots:
        found = None
        for k in range(1, kmax + 1):
            for F in combinations(E, k):
                for b0 in seeds(F):
                    if win(frozenset(F), b0, r):
                        found = (F, b0)
                        break
                if found:
                    break
            if found:
                break
        result[r] = found
    return result


ARGS = {}


def work(line):
    G = nx.from_graph6_bytes(line.encode())
    res = solve_graph(G, ARGS["kmax"], ARGS["roots"], ARGS["general"])
    return line, {r: v for r, v in res.items()}


def init(kmax, roots, general):
    realis._proc = None
    ARGS["kmax"] = kmax
    ARGS["roots"] = roots
    ARGS["general"] = general


def main():
    path = sys.argv[1]
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    roots = sys.argv[3] if len(sys.argv) > 3 else "even"
    general = roots.endswith("+gen")
    roots = roots.replace("+gen", "")
    roots = None if roots == "all" else (roots if roots == "even" else [int(x) for x in roots.split(",")])
    workers = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    lines = [l.strip() for l in open(path) if l.strip()]
    bad = 0
    nroots = 0
    with Pool(workers, initializer=init, initargs=(kmax, roots, general)) as pool:
        for line, res in pool.imap_unordered(work, lines, chunksize=10):
            nroots += len(res)
            losers = [r for r, v in res.items() if v is None]
            if losers:
                bad += 1
                print("LOSE", line, "roots", losers, flush=True)
    print(f"{len(lines)} graphs, {nroots} roots, {bad} graphs with a losing root "
          f"(oracle seeds{', general profiles' if general else ''}, kmax={kmax})", flush=True)


if __name__ == "__main__":
    main()

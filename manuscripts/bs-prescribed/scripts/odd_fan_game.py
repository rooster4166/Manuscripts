"""The Fan game (tools/fan_game.py) at odd order, with an optional prescribed end.

G has odd order N; the budget is N - 1 ends (= floor(N/2) paths).  A play:
  1. Hold an edge set F, K = G - F.  Seeds (all are theorems on K, componentwise):
     (L)  K has at most one vertex of positive even degree: b = d_K mod 2 (Lovasz, exact ends;
          isolated vertices get 0).
     (L3) K' = K minus its isolated vertices has e(K') >= 2 even vertices: for any even u of K',
          b = 1 on odd, 2 on Ev(K') - u, 0 on u and on isolated vertices (Lemma 3, any order:
          endpoint-structure Remark "Lemmas 2 and 3 at every order").
  2. Re-add F by Fan transfers (single, or grouped with adversarial donor), or as a new
     one-edge path (+2 to sum b).
  3. Win: sum b <= N-1, and b(y) >= 1 if a prescribed y is given (or sum b <= N-3: then a path
     can be split at y, which has positive degree).
Soundness: every move is fan_single / fan_grouped / Ach.addPath applied to a partition with the
stated profile, so a win gives a partition of G into at most (N-1)/2 paths (with an end at y).

Usage: python3 odd_fan_game.py FILE.g6 [kmax=4] [mode]
  mode = "pres": every even y with Delta(EV) <= 3 (prescribed-end lemma);
         "plain": no prescription, all graphs given (floor bound).
"""
import sys
from functools import lru_cache
from itertools import combinations

import networkx as nx


def solve(G, y=None, kmax=4, budget=None):
    n = G.number_of_nodes()
    nodes = sorted(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    E = sorted(tuple(sorted((idx[a], idx[b]))) for a, b in G.edges())
    if budget is None:
        budget = 2 * (n // 2)
    yy = None if y is None else idx[y]
    nbr = [0] * n
    for a, b in E:
        nbr[a] |= 1 << b
        nbr[b] |= 1 << a

    def popc(x):
        return bin(x).count("1")

    def key(a, c):
        return (a, c) if a < c else (c, a)

    @lru_cache(maxsize=None)
    def win(rem, b):
        s = sum(b)
        if not rem:
            if yy is None:
                return s <= budget
            return (s <= budget and b[yy] >= 1) or s <= budget - 2
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
                    if win(rest, tuple(nb)):
                        return True
            if s + 2 <= budget:
                nb = list(b); nb[a] += 1; nb[c] += 1
                if win(rest, tuple(nb)):
                    return True
        for u in range(n):
            cands = [t for t in range(n) if key(u, t) in rem]
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
                        nb = list(b); nb[u] += 1; nb[t] -= 1
                        if not win(rem - {key(u, t)}, tuple(nb)):
                            ok = False
                            break
                    if ok:
                        return True
        return False

    def starts(F):
        Fs = set(F)
        deg = [0] * n
        for a, c in E:
            if (a, c) not in Fs:
                deg[a] += 1; deg[c] += 1
        poseven = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
        out = []
        if len(poseven) <= 1:
            out.append(tuple(d % 2 for d in deg))
        if len(poseven) >= 2:
            base = [1 if deg[v] % 2 else (2 if deg[v] > 0 else 0) for v in range(n)]
            if sum(base) - 2 <= budget:
                for u in poseven:
                    bb = list(base); bb[u] = 0
                    out.append(tuple(bb))
        return out

    for k in range(0, kmax + 1):
        for F in combinations(E, k):
            for b0 in starts(F):
                if win(frozenset(F), b0):
                    return (F, b0)
    return None


def ev(G):
    return [v for v in G if G.degree(v) % 2 == 0 and G.degree(v) > 0]


def main():
    path = sys.argv[1]
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    mode = sys.argv[3] if len(sys.argv) > 3 else "pres"
    gs = nx.read_graph6(path)
    if not isinstance(gs, list):
        gs = [gs]
    tested = lost = 0
    for G in gs:
        E = ev(G)
        if mode == "pres":
            H = G.subgraph(E)
            if E and max(dict(H.degree()).values()) > 3:
                continue
            for y in E:
                tested += 1
                if solve(G, y, kmax) is None:
                    lost += 1
                    print("LOSE", nx.to_graph6_bytes(G, header=False).strip().decode(), "y", y,
                          "e", len(E), flush=True)
        else:
            tested += 1
            if solve(G, None, kmax) is None:
                lost += 1
                print("LOSE", nx.to_graph6_bytes(G, header=False).strip().decode(), "e", len(E),
                      flush=True)
    print(f"tested {tested}, lost {lost} (kmax={kmax}, mode={mode})", flush=True)


if __name__ == "__main__":
    main()

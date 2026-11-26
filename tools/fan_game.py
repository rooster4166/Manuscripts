"""The pure Fan game: Lovász's theorem plus Fan's transfers, played on end-count profiles.

Let G have even order n. A play consists of the following steps.
  1. Choose an edge set F and put K = G - F. The start profile b on V is one Lovász guarantees:
     (a) if K has at most one vertex of positive even degree: b = d_K mod 2 (Lovász, strong form);
     (b) if K has no isolated vertex and exactly two even vertices u, v: b = 1 on odd vertices,
         b(v) = 2 and b(u) = 0 (Lemma 3: Ev(K) - u is realisable).
  2. Re-add the edges of F one at a time. The current graph is H; Z_H(u) is the set of
     neighbours of u in H with b = 0. Each step adds edges in one of three ways:
     * single transfer of ut towards u, allowed if b(t) > |Z_H(u)|: b(u) += 1, b(t) -= 1;
     * grouped transfer at u with a set T (|T| >= 2) of remaining F-edges ut, allowed if
       sum_{t in T} b(t) > |Z_H(u)|. The opponent picks t in T with b(t) >= 1, and ut is added
       with b(u) += 1, b(t) -= 1;
     * new one-edge path ut: b(u) += 1, b(t) += 1 (raises sum b by 2).
  3. The play wins for the root r if, once F is used up, sum b <= n and b(r) >= 1.
Soundness: every move is Fan's lemma (`fan_single`, `fan_grouped`; Lean) applied to a realising
partition, so a winning play gives a partition of G into at most n/2 paths with an end at r.
Hence p(G + leaf at r) <= n/2, which is the rooted test R for (G, r).

Inductive variant ("ind"): the seed may also come from the induction hypothesis on a smaller
connected spanning K = G - F (F nonempty). For a chosen r' in Ev(K), the adversary picks any
half-set S' of Ev(K) containing r'; the profile is 1 on odd vertices, 2 on S' and 0 elsewhere.
We must win against every choice of S'. If every connected even-order graph has a winning
inductive play, Gallai follows by induction on the number of edges.

Usage: python3 tools/fan_game.py FILE.g6 [kmax] [ind]
"""
import sys
from functools import lru_cache
from itertools import combinations

import networkx as nx


def solve_graph(G, kmax=4, roots=None, inductive=False):
    n = G.number_of_nodes()
    nodes = sorted(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    E = sorted(tuple(sorted((idx[a], idx[b]))) for a, b in G.edges())
    nbr = [0] * n
    for a, b in E:
        nbr[a] |= 1 << b
        nbr[b] |= 1 << a

    def popc(x):
        return bin(x).count("1")

    @lru_cache(maxsize=None)
    def win(rem, b, r):
        # rem: frozenset of remaining F-edges; b: profile tuple
        s = sum(b)
        if not rem:
            # b(r) >= 1, or room to split a path at r (r has positive degree)
            return (s <= n and b[r] >= 1) or s <= n - 2
        # adjacency of the current graph H = G - rem
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
        # grouped transfers
        for u in range(n):
            cands = [t for t in range(n) if (min(u, t), max(u, t)) in rem]
            if len(cands) < 2:
                continue
            z = Z(u)
            for k in range(2, len(cands) + 1):
                for T in combinations(cands, k):
                    if sum(b[t] for t in T) <= z:
                        continue
                    if all(b[t] == 0 or b[t] > z or True for t in T):
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
        if all(d > 0 for d in deg):
            ev = [v for v in range(n) if deg[v] % 2 == 0]
            if len(ev) == 2:
                for u, v in (ev, ev[::-1]):
                    b = [d % 2 for d in deg]; b[v] = 2; b[u] = 0
                    out.append(tuple(b))
        return out

    def ind_seeds(F):
        """Seeds from the induction hypothesis (simple-profile rooted test) on K = G - F.

        K must be connected and spanning (no isolated vertex). For each choice of r' (an even
        vertex of K, or None), the adversary picks a half-set S' of Ev(K) containing r'.
        Returns a list of (r', [profiles]) pairs: we must win for every profile in the list."""
        Fs = set(F)
        Kg = nx.Graph(); Kg.add_nodes_from(range(n))
        Kg.add_edges_from(e for e in E if e not in Fs)
        if not nx.is_connected(Kg):
            return []
        deg = [Kg.degree(v) for v in range(n)]
        ev = [v for v in range(n) if deg[v] % 2 == 0]
        h = len(ev) // 2
        out = []
        for rp in [None] + ev:
            profs = []
            for Sp in combinations(ev, h):
                if rp is not None and rp not in Sp:
                    continue
                b = [d % 2 for d in deg]
                for v in Sp:
                    b[v] = 2
                profs.append(tuple(b))
            out.append((rp, profs))
        return out

    roots = range(n) if roots is None else roots
    result = {}
    for r in roots:
        found = None
        for k in range(0, kmax + 1):
            for F in combinations(E, k):
                for b0 in starts(F):
                    if win(frozenset(F), b0, r):
                        found = (F, b0)
                        break
                if found:
                    break
                if inductive and k >= 1:
                    for rp, profs in ind_seeds(F):
                        if all(win(frozenset(F), b0, r) for b0 in profs):
                            found = (F, ("IH", rp))
                            break
                if found:
                    break
            if found:
                break
        result[r] = found
    return result


def main():
    path = sys.argv[1]
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    inductive = len(sys.argv) > 3 and sys.argv[3] == "ind"
    graphs = nx.read_graph6(path)
    if not isinstance(graphs, list):
        graphs = [graphs]
    bad = 0
    for G in graphs:
        res = solve_graph(G, kmax, inductive=inductive)
        losers = [r for r, v in res.items() if v is None]
        if losers:
            bad += 1
            d = dict(G.degree())
            print("LOSE", nx.to_graph6_bytes(G, header=False).strip().decode(), sorted(G.edges()),
                  "Ev", [v for v in G if d[v] % 2 == 0], "roots", losers, flush=True)
    print(f"{len(graphs)} graphs, {bad} with a losing root (kmax={kmax})", flush=True)


if __name__ == "__main__":
    main()

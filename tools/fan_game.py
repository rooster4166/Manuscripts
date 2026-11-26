"""The Fan game: Lovász's theorem plus Fan's transfers, played on end-count profiles.

Let G have even order n. A play consists of the following steps.
  1. Choose an edge set F and put K = G - F. The start profile b on V is one Lovász guarantees:
     (a) if K has at most one vertex of positive even degree: b = d_K mod 2 (Lovász, strong form);
     (b) if K has no isolated vertex and exactly two even vertices u, v: b = 1 on odd vertices,
         b(v) = 2 and b(u) = 0 (Lemma 3: Ev(K) - u is realisable).
  2. Re-add the edges of F. The current graph is H = G - rem, where rem is the set of edges still
     held; Z_H(u) is the set of neighbours of u in H with b = 0. The moves are:
     * single transfer of ut towards u, allowed if b(t) > |Z_H(u)|: b(u) += 1, b(t) -= 1;
     * grouped transfer at u with a set T (|T| >= 2) of remaining F-edges ut, allowed if
       sum_{t in T} b(t) > |Z_H(u)|. The opponent picks t in T with b(t) >= 1, and ut is added
       with b(u) += 1, b(t) -= 1;
     * new one-edge path ut: b(u) += 1, b(t) += 1 (raises sum b by 2);
     * [option "np"] new path: any path P of length >= 2 all of whose edges are held is added as
       one new path: b += 1 at each end of P (raises sum b by 2). Soundness: D + P.
     * [option "rotR"] rotation (Pósa) of a held edge uv with b(v) >= 1, at most R times in a
       play. Either some path ending at v avoids u, and uv is appended (b(u) += 1, b(v) -= 1),
       or all b(v) of them pass through u; their predecessors of u (read from v) form a set
       W of b(v) neighbours of u in H chosen by the opponent, we pick w in W, and the path is
       rotated: H becomes H + uv - uw (uw is now held instead of uv), b(v) -= 1, b(w) += 1.
       Soundness: `rotation_or_append` (lean/GallaiLean/MissingMove.lean).
  3. The play wins for the root r if, once F is used up, sum b <= n and b(r) >= 1.
Soundness: every move is Fan's lemma (`fan_single`, `fan_grouped`), `Ach.addPath`, or the
rotation lemma, applied to a realising partition, so a winning play gives a partition of G into
at most n/2 paths with an end at r. Hence p(G + leaf at r) <= n/2, which is the rooted test R.

Inductive variant ("ind"): the seed may also come from the induction hypothesis on a smaller
connected spanning K = G - F (F nonempty). For a chosen r' in Ev(K), the adversary picks any
half-set S' of Ev(K) containing r'; the profile is 1 on odd vertices, 2 on S' and 0 elsewhere.
We must win against every choice of S'. If every connected even-order graph has a winning
inductive play, Gallai follows by induction on the number of edges.

Usage: python3 tools/fan_game.py FILE.g6 [kmax] [ind] [np] [rotR] [altR] [hubs]
  e.g. python3 tools/fan_game.py data/conn8.g6 4 np      (Fan + multi-edge new paths)
       python3 tools/fan_game.py FILE 4 rot2              (Fan + at most two rotations)
       python3 tools/fan_game.py FILE 2 np hubs           (F = a full star plus <= 2 edges)
Without "np", "rotR" and "altR" the game is the original one of experiments E13. With "hubs",
kmax counts the edges held besides one full star.
"""
import sys
from functools import lru_cache
from itertools import combinations

import networkx as nx


def solve_graph(G, kmax=4, roots=None, inductive=False, newpath=False, rot=0, alt=0, hubs=False):
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

    def key(a, c):
        return (a, c) if a < c else (c, a)

    @lru_cache(maxsize=None)
    def win(rem, b, r, R=0, A=0):
        # rem: frozenset of held edges; b: profile tuple; R, A: rotations / activations left
        s = sum(b)
        if not rem:
            return s <= n and b[r] >= 1
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
                    if win(rest, tuple(nb), r, R, A):
                        return True
            if s + 2 <= n:
                nb = list(b); nb[a] += 1; nb[c] += 1
                if win(rest, tuple(nb), r, R, A):
                    return True
        # new paths of length >= 2 made of held edges
        if newpath and s + 2 <= n:
            radj = {}
            for a, c in rem:
                radj.setdefault(a, []).append(c)
                radj.setdefault(c, []).append(a)

            def dfs(path, used):
                if len(path) >= 3 and path[0] < path[-1]:
                    nb = list(b); nb[path[0]] += 1; nb[path[-1]] += 1
                    if win(rem - used, tuple(nb), r, R, A):
                        return True
                for w in radj.get(path[-1], ()):
                    if w in path:
                        continue
                    if dfs(path + [w], used | {key(path[-1], w)}):
                        return True
                return False

            for v0 in radj:
                if dfs([v0], frozenset()):
                    return True
        # rotations: uv held, b(v) >= 1; the direct outcome must win, and fewer than b(v)
        # neighbours w of u in H may lose after rotating to H + uv - uw.
        if R > 0:
            for (a, c) in rem:
                rest = rem - {(a, c)}
                for u, v in ((a, c), (c, a)):
                    if b[v] == 0:
                        continue
                    if b[v] > Z(u):
                        continue  # Fan's single transfer already covers this edge
                    nb = list(b); nb[u] += 1; nb[v] -= 1
                    if not win(rest, tuple(nb), r, R, A):
                        continue
                    losing = 0
                    Nu = nbr[u] & ~remmask[u]
                    for w in range(n):
                        if not (Nu >> w) & 1:
                            continue
                        nb = list(b); nb[v] -= 1; nb[w] += 1
                        if not win(rest | {key(u, w)}, tuple(nb), r, R - 1, A):
                            losing += 1
                            if losing >= b[v]:
                                break
                    if losing < b[v]:
                        return True
        # Fan's alternative at or below equality (option "altR"): for a set T of held edges ut
        # with 1 <= sum_T b <= |Z(u)|, either some t in T transfers (the opponent picks t), or
        # some set W of at least sum_T b blank neighbours of u is reachable; we pick z in W,
        # the opponent picks a t in T, and the end moves from t to z while the held edge ut is
        # replaced by uz (z is now held, tu is present). At most R activations per play.
        if A > 0:
            for u in range(n):
                cands = [t for t in range(n) if key(u, t) in rem and b[t] >= 1]
                if not cands:
                    continue
                Hu = nbr[u] & ~remmask[u]
                blanks = [w for w in range(n) if (Hu >> w) & 1 and b[w] == 0]
                zu = len(blanks)
                for k in range(1, len(cands) + 1):
                    for T in combinations(cands, k):
                        sT = sum(b[t] for t in T)
                        if sT > zu:
                            continue  # Fan applies
                        ok = True
                        for t in T:
                            nb = list(b); nb[u] += 1; nb[t] -= 1
                            if not win(rem - {key(u, t)}, tuple(nb), r, R, A):
                                ok = False
                                break
                        if not ok:
                            continue
                        bad = 0
                        for zz in blanks:
                            for t in T:
                                nb = list(b); nb[t] -= 1; nb[zz] += 1
                                if not win((rem - {key(u, t)}) | {key(u, zz)}, tuple(nb), r, R,
                                           A - 1):
                                    bad += 1
                                    break
                            if bad >= sT:
                                break
                        if bad < sT:
                            return True
        # grouped transfers
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
                        if not win(rem - {key(u, t)}, tuple(nb), r, R, A):
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

    def hub_sets(k):
        """Held sets of the form star(h) + k further edges (option "hubs"; for n >= 10)."""
        seen = set()
        for h in range(n):
            star = [e for e in E if h in e]
            rest = [e for e in E if h not in e]
            for X in combinations(rest, k):
                F = tuple(sorted(star + list(X)))
                if F not in seen:
                    seen.add(F)
                    yield F

    roots = range(n) if roots is None else roots
    result = {}
    for r in roots:
        found = None
        for k in range(0, kmax + 1):
            for F in (hub_sets(k) if hubs else combinations(E, k)):
                for b0 in starts(F):
                    if win(frozenset(F), b0, r, rot, alt):
                        found = (F, b0)
                        break
                if found:
                    break
                if inductive and k >= 1:
                    for rp, profs in ind_seeds(F):
                        if all(win(frozenset(F), b0, r, rot, alt) for b0 in profs):
                            found = (F, ("IH", rp))
                            break
                if found:
                    break
            if found:
                break
        result[r] = found
        win.cache_clear()
    return result


def parse_opts(args):
    kmax, inductive, newpath, rot, alt, hubs = 4, False, False, 0, 0, False
    for a in args:
        if a == "ind":
            inductive = True
        elif a == "hubs":
            hubs = True
        elif a == "np":
            newpath = True
        elif a.startswith("rot"):
            rot = int(a[3:] or 1)
        elif a.startswith("alt"):
            alt = int(a[3:] or 1)
        else:
            kmax = int(a)
    return kmax, inductive, newpath, rot, alt, hubs


def main():
    path = sys.argv[1]
    kmax, inductive, newpath, rot, alt, hubs = parse_opts(sys.argv[2:])
    graphs = nx.read_graph6(path)
    if not isinstance(graphs, list):
        graphs = [graphs]
    bad = 0
    for G in graphs:
        res = solve_graph(G, kmax, inductive=inductive, newpath=newpath, rot=rot, alt=alt,
                          hubs=hubs)
        losers = [r for r, v in res.items() if v is None]
        if losers:
            bad += 1
            d = dict(G.degree())
            print("LOSE", nx.to_graph6_bytes(G, header=False).strip().decode(), sorted(G.edges()),
                  "Ev", [v for v in G if d[v] % 2 == 0], "roots", losers, flush=True)
    opts = f"kmax={kmax}" + (", ind" if inductive else "") + (", np" if newpath else "") + \
        (f", rot{rot}" if rot else "") + (f", alt{alt}" if alt else "") + (", hubs" if hubs else "")
    print(f"{len(graphs)} graphs, {bad} with a losing root ({opts})", flush=True)


if __name__ == "__main__":
    main()

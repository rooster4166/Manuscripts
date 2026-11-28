"""A38: overview Thm 3.18 at order 8 (independent of test2/scripts/dz4_cover.py).
Instances: 3-connected J of order 8 with exactly two even vertices z ~ r (both orientations),
d(z) = 4.  Data: N(z) - r = {w, a, b} with ab an edge (choice of w).  Covered if, for some data
choice and orientation (a, b):
  FAR  : a, b have no common neighbour in J - z (separation), or
  STEER: ((J - z) - ab, b, {a}) has a two-token schedule (trn Def 6.3 / Lean Steer2): leaf l at b,
         X = {l, a}, tokens at w and b; a move of the token at p deletes pu with u not in X, u not the
         other token and u not adjacent to the other token afterwards; it retires if u is isolated;
         a schedule ends with a retirement.
Also checks the conclusion directly: an exact search for a Lovasz decomposition of (J - z) - ab
with a not on the path ending at b (the hypothesis of Thm 3.18), for every instance with data.
input: nauty-geng -q -c -d3 8 on stdin."""
import sys
from collections import Counter
from functools import lru_cache
import networkx as nx
from a38lib import G, find_decomp, norm


def steer2(edges, n, w, b, a):
    ell = n  # new leaf
    E0 = frozenset(edges) | {norm(b, ell)}
    X = {ell, a}

    def adj(E, v):
        return [y if x == v else x for (x, y) in E if v in (x, y)]

    seen = set()

    def rec(E, p, q):
        key = (E, p, q)
        if key in seen:
            return False
        seen.add(key)
        for (mover, other) in ((p, q), (q, p)):
            for u in adj(E, mover):
                if u in X or u == other:
                    continue
                E2 = E - {norm(mover, u)}
                nb = adj(E2, u)
                if other in nb:
                    continue
                if not nb:
                    return True  # retirement
                if rec(E2, u, other) if mover == p else rec(E2, other, u):
                    return True
        return False
    return rec(E0, w, b)


def main():
    cnt = Counter()
    for line in sys.stdin:
        s = line.strip()
        H = nx.from_graph6_bytes(s.encode())
        ev = [v for v in H if H.degree(v) % 2 == 0]
        if len(ev) != 2 or not H.has_edge(*ev) or nx.node_connectivity(H) < 3:
            continue
        for z, r in (tuple(ev), tuple(reversed(ev))):
            cnt["inst_all"] += 1
            if H.degree(z) != 4:
                continue
            cnt["inst"] += 1
            T = [v for v in H[z] if v != r]
            datas = []
            for w in T:
                a, b = [v for v in T if v != w]
                if H.has_edge(a, b):
                    datas.append((w, a, b))
            if not datas:
                cnt["nodata"] += 1
                continue
            cnt["data"] += 1
            Bz = [e for e in H.edges() if z not in e]
            far = steer = direct = False
            for (w, a, b) in datas:
                if not (set(H[a]) & set(H[b]) - {z}):
                    far = True
                K = [norm(*e) for e in Bz if set(e) != {a, b}]
                for (x, y) in ((a, b), (b, a)):  # Q(y) avoids x
                    if steer2(K, H.number_of_nodes(), w, y, x):
                        steer = True
                    g = G(H.number_of_nodes(), K)
                    cap = [g.deg(v) % 2 for v in range(g.n)]
                    D = find_decomp(g, sum(cap) // 2, cap,
                                    lambda P, x=x, y=y: not (y in (P[0], P[-1]) and x in P))
                    if D is not None:
                        direct = True
            cnt["FAR"] += far
            cnt["STEER_not_FAR"] += (steer and not far)
            cnt["STEER"] += steer
            cnt["covered"] += (far or steer)
            cnt["hypothesis_holds"] += direct
    for k in sorted(cnt):
        print(k, cnt[k])


if __name__ == "__main__":
    main()

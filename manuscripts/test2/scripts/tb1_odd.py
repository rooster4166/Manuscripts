"""tb1_odd.py: the all-odd base for (T1), the twin of the (T2) forest lift (test2 session).

(T1) at (J, z, r): z is the only even vertex of J, r in N(z); J - z needs a decomposition into at
most (n - 1)/2 paths with at least two ends at r.  With T = N(z) (the even vertices of J - z, r
included) and a forest T-join Phi of J - z rooted with r a root, H = (J - z) - Phi has no even
vertex.  The all-odd base asks for a Lovasz decomposition of H with (i) the path ending at each
child v avoids p(v), (ii) siblings end distinct paths (Lean `twoEnds_of_oddBase`,
`test1At_of_oddBase`; matching case `test1At_of_matchingOdd`).  Searched exactly with
tools/route_ext.c query C (masks {v, p(v)} at the children), in tiers:
  M : Phi a perfect matching of J[N(z)] (r a root of its pair, all orientations of the others);
  S : Phi the T-join inside a spanning tree of J - z (BFS trees from every vertex, then random
      trees), r a root;
  C : as S, with r a child having at least two children (then r ends c(r) >= 2 paths; this case
      is proved on paper, not in Lean).
Every base found is checked, the forest is appended, and the result is verified as a (T1)
decomposition (path partition of J - z, <= (n-1)/2 paths, >= 2 ends at r).
Input: graph6 lines; keeps the 3-connected J with exactly one even vertex.
usage: python3 tb1_odd.py ROUTE_EXT [trees] < graphs
"""
import random
import sys
from collections import Counter

import networkx as nx

from tb2 import Oracle, parse_paths, perfect_matchings, rootings, tjoin_in_tree


def three_connected(J):
    n = J.number_of_nodes()
    if n < 4:
        return False
    for a in range(n):
        for b in range(a + 1, n):
            H = J.copy()
            H.remove_nodes_from([a, b])
            if not nx.is_connected(H):
                return False
    return nx.is_connected(J)


def query(H, n, z, par):
    E = list(H.edges())
    b = [0 if v == z else 1 for v in range(n)]
    masks = [(1 << v) | ((1 << par[v]) if v in par else 0) for v in range(n)]
    return f"WC {n} {len(E)} " + " ".join(f"{u} {v}" for u, v in E) + " " + \
        " ".join(map(str, b)) + " " + " ".join(map(str, masks))


def check_and_lift(J, z, r, H, par, order, D0):
    n = J.number_of_nodes()
    used, ends = set(), [0] * n
    for P in D0:
        assert len(P) >= 2 and len(set(P)) == len(P)
        for a, c in zip(P, P[1:]):
            assert H.has_edge(a, c)
            e = frozenset((a, c))
            assert e not in used
            used.add(e)
        ends[P[0]] += 1
        ends[P[-1]] += 1
    assert len(used) == H.number_of_edges()
    assert all(ends[v] == (0 if v == z else 1) for v in range(n))
    Q = {}
    for P in D0:
        Q[P[0]] = P
        Q[P[-1]] = P
    for v, p in par.items():
        assert p not in Q[v], ("(i)", v, p)
    for x in par:
        for y in par:
            if x < y and par[x] == par[y]:
                assert Q[x] is not Q[y], ("(ii)", x, y)
    paths = [list(P) for P in D0]
    for v in order:
        p = par[v]
        idx = [i for i, P in enumerate(paths) if P[0] == v or P[-1] == v]
        assert len(idx) == 1
        P = paths[idx[0]]
        if P[0] == v:
            P.insert(0, p)
        else:
            P.append(p)
        assert len(set(P)) == len(P)
    # verify (T1)
    B = J.copy()
    B.remove_node(z)
    used, er = set(), 0
    for P in paths:
        for a, c in zip(P, P[1:]):
            assert B.has_edge(a, c)
            e = frozenset((a, c))
            assert e not in used
            used.add(e)
        er += (P[0] == r) + (P[-1] == r)
    assert len(used) == B.number_of_edges()
    assert len(paths) <= (n - 1) // 2 and er >= 2
    return er


def main():
    oracle = Oracle(sys.argv[1])
    ntrees = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    rng = random.Random(1)
    st = Counter()
    for g6 in sys.stdin:
        g6 = g6.strip()
        if not g6:
            continue
        J = nx.from_graph6_bytes(g6.encode())
        n = J.number_of_nodes()
        ev = [v for v in J if J.degree(v) % 2 == 0]
        if len(ev) != 1 or min(d for _, d in J.degree()) < 3 or not three_connected(J):
            continue
        z = ev[0]
        T = sorted(J[z])
        B = J.copy()
        B.remove_node(z)
        st["graphs"] += 1
        for r in T:
            st["instances"] += 1
            found = None
            pms = list(perfect_matchings(T, J))
            if pms:
                st["with matching data"] += 1
            for pm in pms:
                for par, order in rootings(pm, r, 10 ** 6):
                    H = B.copy()
                    H.add_node(z)
                    H.remove_edges_from(pm)
                    o = oracle.query(query(H, n, z, par))
                    assert o[0] in "01", o
                    if o.startswith("1"):
                        found = ("M", check_and_lift(J, z, r, H, par, order, parse_paths(o)))
                        break
                if found:
                    break
            if not found:
                trees = [nx.bfs_tree(B, s).to_undirected() for s in B]
                for _ in range(ntrees):
                    w = {e: rng.random() for e in B.edges()}
                    nx.set_edge_attributes(B, w, "w")
                    trees.append(nx.minimum_spanning_tree(B, weight="w"))
                phis, seen = [], set()
                for S in trees:
                    phi = tjoin_in_tree(S, T)
                    key = frozenset(frozenset(e) for e in phi)
                    if key not in seen:
                        seen.add(key)
                        phis.append(phi)
                for tier, nonroot in (("S", False), ("C", True)):
                  if found:
                    break
                  for phi in phis:
                    for par, order in rootings(phi, r, 50, nonroot=nonroot):
                        H = B.copy()
                        H.add_node(z)
                        H.remove_edges_from(phi)
                        assert all(H.degree(v) % 2 == 1 for v in H if v != z)
                        o = oracle.query(query(H, n, z, par))
                        assert o[0] in "01", o
                        if o.startswith("1"):
                            found = (tier, check_and_lift(J, z, r, H, par, order, parse_paths(o)))
                            break
                    if found:
                        break
            if found:
                st["base " + found[0]] += 1
                st[f"ends at r = {found[1]}"] += 1
            else:
                st["no base found"] += 1
                print("NOBASE", g6, z, r, flush=True)
    print("SUMMARY", dict(st), file=sys.stderr)


if __name__ == "__main__":
    main()

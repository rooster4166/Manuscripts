"""dz4_cover.py: (T2) at deletion degree 4 from proved theorems, through the floor lift (test2).

At d(z) = 4, N(z) = {r, w, a, b}.  If ab is an edge, the floor-lift data are (w, {ab}) and the base is
one DL(1) pair in G = (J - z) - ab, whose only even vertex is w: a Lovasz decomposition of G with
a not in Q(b) or b not in Q(a).  That gives the floor for J - z, hence (T2).  Proved routes to it:
  FAR   : a, b have no common neighbour in G         (separation, pair form; Lean `separation`);
  STEER : a two-token schedule exists for (G, y, {x}) with {x, y} = {a, b}
          (trn session, Lean `avoid_of_steer2`; the search is a port of trn/scripts/steer2.cpp).
Every STEER answer is cross-checked with the exact oracle (route_ext A query: some Lovasz
decomposition of G has Q(y) avoiding x).  FAR answers are not cross-checked (FAR is a proved theorem).  Reports, per instance with d(z) = 4, whether some data
choice is settled by FAR or STEER, and whether data exist at all.
usage: python3 dz4_cover.py ORACLE BUDGET < t2_fields
"""
import sys
from collections import Counter

import networkx as nx

from tb2 import Oracle


class Budget(Exception):
    pass


def steer2(adj0, g, y, x, budget):
    """Port of steer2.cpp: tokens at g and y (a leaf hangs at y); a step moves a token from p along
    an unused edge pq to q, q not x, not the other token, and not adjacent (after removing pq) to
    the other token; a token is done when it reaches an isolated vertex (y is never isolated).
    Returns True if some token can be made done."""
    fail = set()
    nodes = [0]

    def search(pg, py, adj):
        if pg < 0 or py < 0:
            return True
        nodes[0] += 1
        if nodes[0] > budget:
            raise Budget
        key = (adj, pg, py)
        if key in fail:
            return False
        for tok in (0, 1):
            p, o = (pg, py) if tok == 0 else (py, pg)
            if p < 0:
                continue
            nb = adj[p]
            while nb:
                q = (nb & -nb).bit_length() - 1
                nb &= nb - 1
                if q == x or q == o:
                    continue
                a2 = list(adj)
                a2[p] &= ~(1 << q)
                a2[q] &= ~(1 << p)
                if o >= 0 and (a2[q] >> o) & 1:
                    continue
                nq = q if (a2[q] or q == y) else -1
                res = search(nq, py, tuple(a2)) if tok == 0 else search(pg, nq, tuple(a2))
                if res:
                    return True
        fail.add(key)
        return False

    try:
        return search(g, y, tuple(adj0))
    except Budget:
        return None


def avoid_query(G, n, y, x):
    E = list(G.edges())
    b = [G.degree(v) % 2 for v in range(n)]
    xs = [0] * n
    xs[y] = 1 << x
    return f"A {n} {len(E)} " + " ".join(f"{u} {v}" for u, v in E) + " " + \
        " ".join(map(str, b)) + " " + " ".join(map(str, xs))


def main():
    oracle = Oracle(sys.argv[1])
    budget = int(sys.argv[2])
    stats = Counter()
    for line in sys.stdin:
        f = line.split()
        if len(f) < 3:
            continue
        g6, z, r = f[0], int(f[1]), int(f[2])
        J = nx.from_graph6_bytes(g6.encode())
        if J.degree(z) != 4:
            continue
        n = J.number_of_nodes()
        stats["d(z)=4 instances"] += 1
        U = [u for u in J[z] if u != r]
        data = []
        for w in U:
            a, b = [u for u in U if u != w]
            if J.has_edge(a, b):
                data.append((w, a, b))
        if not data:
            stats["no data"] += 1
            continue
        stats["with data"] += 1
        how = None
        for w, a, b in data:
            G = J.copy()
            G.remove_node(z)
            G.add_node(z)  # keep labels; z isolated
            G.remove_edge(a, b)
            if not (set(G[a]) & set(G[b])):
                how = "FAR"
                break
            adj = [0] * n
            for u, v in G.edges():
                adj[u] |= 1 << v
                adj[v] |= 1 << u
            for y, x in ((b, a), (a, b)):
                s = steer2(adj, w, y, x, budget)
                if s:
                    o = oracle.query(avoid_query(G, n, y, x))
                    assert o.startswith("1"), ("schedule but no avoidance?", g6, z, r, w, y, x)
                    how = "STEER"
                    break
                if s is None:
                    stats["budget hits"] += 1
            if how:
                break
        stats[how or "not covered"] += 1
    for k in sorted(stats):
        print(k, stats[k])


if __name__ == "__main__":
    main()

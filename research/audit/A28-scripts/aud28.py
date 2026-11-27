"""A28 auditor checks (independent of tools/route_ext.c and of the project's scripts).

1. data:   in K6 - D, D in {empty, K2, P3, K3, C4}, every root r admits (w, M0).
2. cex:    J = K_{3,4} + x1x2 is 3-connected, z its only even vertex, N(z) independent: no data.
3. equiv:  for random small J and every data choice (r, w, M0):
             LHS  M has a Lovasz decomposition with (2.1) for every pair  (brute force)
             RHS  J - z has a decomposition into <= k paths, >= 2 ends at r, in which every
                  edge of M0 is the first or last edge of its path              (brute force)
           and also T1 at r without the terminal condition.
"""
import itertools
import random
import sys
from functools import lru_cache

import networkx as nx


# ---------------------------------------------------------------- 1. data availability
def data_choices(J, z, r):
    U = sorted(J.neighbors(z))
    out = []
    for w in U:
        if w == r:
            continue
        rest = [u for u in U if u not in (r, w)]
        for pm in pms(rest, J):
            out.append((w, pm))
    return out


def pms(vs, J):
    if not vs:
        yield []
        return
    a = vs[0]
    for b in vs[1:]:
        if J.has_edge(a, b):
            for pm in pms([v for v in vs[1:] if v != b], J):
                yield [(a, b)] + pm


def check_data():
    shapes = {"empty": [], "K2": [(0, 1)], "P3": [(0, 1), (1, 2)], "K3": [(0, 1), (1, 2), (0, 2)],
              "C4": [(0, 1), (1, 2), (2, 3), (3, 0)]}
    ok = True
    for name, D in shapes.items():
        J = nx.complete_graph(range(1, 7))
        J.remove_edges_from([(a + 1, b + 1) for a, b in D])
        J.add_edges_from((0, u) for u in range(1, 7))
        per = {r: len(data_choices(J, 0, r)) for r in range(1, 7)}
        print("data", name, per)
        ok &= all(v > 0 for v in per.values())
    print("DATA every root of every dense shape:", ok)


# ---------------------------------------------------------------- 2. counterexample
def check_cex():
    J = nx.complete_bipartite_graph(3, 4)   # 0,1,2 | 3,4,5,6
    J.add_edge(1, 2)                          # x1 x2
    z = 0
    degs = dict(J.degree())
    even = [v for v in J if degs[v] % 2 == 0]
    print("cex: n=%d degrees=%s even=%s kappa=%d mindeg=%d" % (
        J.number_of_nodes(), degs, even, nx.node_connectivity(J), min(degs.values())))
    print("cex: N(z)=%s independent=%s data per root=%s" % (
        sorted(J.neighbors(z)), not any(J.has_edge(a, b) for a, b in itertools.combinations(J.neighbors(z), 2)),
        {r: len(data_choices(J, z, r)) for r in J.neighbors(z)}))


# ---------------------------------------------------------------- brute-force searches
def lovasz_disj(M_edges, n, b, pairs):
    """Exists a decomposition of M into paths with exactly b[v] ends at v and, for every pair
    (a, c), the path ending at c avoids a or the path ending at a avoids c?"""
    E = list(M_edges)
    eid = {}
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(E):
        eid[(u, v)] = eid[(v, u)] = i
        adj[u].append((v, i))
        adj[v].append((u, i))
    full = (1 << len(E)) - 1
    for orient in itertools.product([0, 1], repeat=len(pairs)):
        avoid = [0] * n
        for (a, c), o in zip(pairs, orient):
            if o == 0:
                avoid[c] |= 1 << a
            else:
                avoid[a] |= 1 << c
        fail = set()

        def solve(rem, bb):
            key = (rem, bb)
            if rem == 0:
                return all(x == 0 for x in bb)
            if key in fail:
                return False
            bl = list(bb)
            starts = [v for v in range(n) if bl[v] > 0]
            if not starts:
                fail.add(key)
                return False
            s = starts[0]
            # grow a path from s
            stack = [(s, 1 << s, rem)]

            def grow(c, vis, rem2):
                for (w, i) in adj[c]:
                    if not (rem2 >> i) & 1 or (vis >> w) & 1:
                        continue
                    r3 = rem2 & ~(1 << i)
                    vis2 = vis | (1 << w)
                    if bl[w] > 0 and (vis2 & avoid[w]) == 0 and (vis2 & avoid[s]) == 0:
                        bl[s] -= 1
                        bl[w] -= 1
                        ok = solve(r3, tuple(bl))
                        bl[s] += 1
                        bl[w] += 1
                        if ok:
                            return True
                    if grow(w, vis2, r3):
                        return True
                return False

            if grow(s, 1 << s, rem):
                return True
            fail.add(key)
            return False

        if solve(full, tuple(b)):
            return True
    return False


def t1_terminal(B_edges, verts, r, k, term_edges):
    """Exists a decomposition of B into <= k paths with >= 2 ends at r in which every edge of
    term_edges is the first or last edge of its path?  No end profile is prescribed."""
    idx = {v: i for i, v in enumerate(verts)}
    n = len(verts)
    E = [(idx[u], idx[v]) for u, v in B_edges]
    T = set()
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(E):
        adj[u].append((v, i))
        adj[v].append((u, i))
    for a, c in term_edges:
        for i, (u, v) in enumerate(E):
            if {u, v} == {idx[a], idx[c]}:
                T.add(i)
    R = idx[r]
    full = (1 << len(E)) - 1
    inc = [0] * n
    for i, (u, v) in enumerate(E):
        inc[u] |= 1 << i
        inc[v] |= 1 << i
    fail = set()

    def odd_count(rem):
        return sum(1 for v in range(n) if bin(rem & inc[v]).count("1") % 2)

    def solve(rem, used, er):
        if rem == 0:
            return er >= 2
        key = (rem, used, er)
        if key in fail:
            return False
        oc = odd_count(rem)
        need = max(1, (oc + 1) // 2)
        if used + need > k:
            fail.add(key)
            return False
        odd = [v for v in range(n) if bin(rem & inc[v]).count("1") % 2]
        starts = [odd[0]] if odd else [v for v in range(n) if rem & inc[v]]
        for s in starts:
            def grow(c, vis, rem2, elist):
                for (w, i) in adj[c]:
                    if not (rem2 >> i) & 1 or (vis >> w) & 1:
                        continue
                    r3 = rem2 & ~(1 << i)
                    el = elist + [i]
                    # interior terminal edges are forbidden: an edge of T may only be first or last
                    if len(el) >= 3 and el[-2] in T:
                        continue
                    if len(el) >= 2 and el[0] in T and False:
                        pass
                    # close here?
                    if all((e not in T) or j == 0 or j == len(el) - 1 for j, e in enumerate(el)):
                        e2 = er + (1 if s == R else 0) + (1 if w == R else 0)
                        if solve(r3, used + 1, min(e2, 2)):
                            return True
                    if grow(w, vis | (1 << w), r3, el):
                        return True
                return False

            if grow(s, 1 << s, rem, []):
                return True
        fail.add(key)
        return False

    return solve(full, 0, 0)


def gen_J(n, d, rng, p=0.45, pdense=0.6):
    while True:
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(10 ** 9))
        G.remove_edges_from(list(G.edges(0)))
        U = rng.sample(range(1, n), d)
        for u in U:
            G.add_edge(0, u)
        for a, c in itertools.combinations(U, 2):
            if rng.random() < pdense:
                G.add_edge(a, c)
            elif G.has_edge(a, c):
                G.remove_edge(a, c)
        bad = [v for v in range(1, n) if G.degree(v) % 2 == 0]
        rng.shuffle(bad)
        for i in range(0, len(bad), 2):
            u, v = bad[i], bad[i + 1]
            if G.has_edge(u, v):
                G.remove_edge(u, v)
            else:
                G.add_edge(u, v)
        if G.degree(0) != d or any(G.degree(v) % 2 == 0 for v in range(1, n)):
            continue
        if min(dd for _, dd in G.degree()) < 3 or not nx.is_connected(G):
            continue
        return G


def check_equiv(n, d, count, seed):
    rng = random.Random(seed)
    stats = dict(choices=0, both=0, neither=0, lhs_only=0, rhs_only=0, roots=0,
                 t1=0, t1_no_base=0, base_root=0)
    for t in range(count):
        J = gen_J(n, d, rng)
        z = 0
        k = (n - 1) // 2
        B = J.copy()
        B.remove_node(z)
        Bv = sorted(B.nodes())
        for r in sorted(J.neighbors(z)):
            stats["roots"] += 1
            t1 = t1_terminal(list(B.edges()), Bv, r, k, [])
            stats["t1"] += int(t1)
            anybase = False
            for w, pm in data_choices(J, z, r):
                M = J.copy()
                M.remove_edges_from([(z, w)] + [(z, x) for p in pm for x in p] + pm)
                b = [M.degree(v) % 2 for v in range(n)]
                lhs = lovasz_disj(list(M.edges()), n, b, pm)
                rhs = t1_terminal(list(B.edges()), Bv, r, k, pm)
                stats["choices"] += 1
                if lhs and rhs:
                    stats["both"] += 1
                elif not lhs and not rhs:
                    stats["neither"] += 1
                elif lhs:
                    stats["lhs_only"] += 1
                    print("DISAGREE lhs_only", list(J.edges()), r, w, pm, flush=True)
                else:
                    stats["rhs_only"] += 1
                    print("DISAGREE rhs_only", list(J.edges()), r, w, pm, flush=True)
                anybase |= lhs
            stats["base_root"] += int(anybase)
            if t1 and not anybase and data_choices(J, z, r):
                stats["t1_no_base"] += 1
                print("T1 but no base for any data:", list(J.edges()), "r", r, flush=True)
        print(t, n, d, stats, flush=True)
    print("FINAL", n, d, stats, flush=True)


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "data":
        check_data()
    elif mode == "cex":
        check_cex()
    elif mode == "equiv":
        check_equiv(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))


def check_atlas():
    """All graphs of order 7 (networkx atlas) with exactly one even vertex z, d(z) >= 4,
    minimum degree >= 3; z relabelled to 0."""
    from networkx.generators.atlas import graph_atlas_g
    stats = dict(graphs=0, choices=0, both=0, neither=0, lhs_only=0, rhs_only=0, roots=0, t1=0,
                 t1_no_base=0, base_root=0, nodata_root=0, conn3=0)
    for G in graph_atlas_g():
        if G.number_of_nodes() != 7:
            continue
        degs = dict(G.degree())
        even = [v for v in G if degs[v] % 2 == 0]
        if len(even) != 1 or min(degs.values()) < 3:
            continue
        z0 = even[0]
        perm = {z0: 0}
        nxt = 1
        for v in sorted(G):
            if v != z0:
                perm[v] = nxt
                nxt += 1
        J = nx.relabel_nodes(G, perm)
        stats["graphs"] += 1
        stats["conn3"] += int(nx.node_connectivity(J) >= 3)
        n = 7
        k = 3
        B = J.copy()
        B.remove_node(0)
        Bv = sorted(B.nodes())
        for r in sorted(J.neighbors(0)):
            stats["roots"] += 1
            t1 = t1_terminal(list(B.edges()), Bv, r, k, [])
            stats["t1"] += int(t1)
            dc = data_choices(J, 0, r)
            if not dc:
                stats["nodata_root"] += 1
            anybase = False
            for w, pm in dc:
                M = J.copy()
                M.remove_edges_from([(0, w)] + [(0, x) for p in pm for x in p] + pm)
                b = [M.degree(v) % 2 for v in range(n)]
                lhs = lovasz_disj(list(M.edges()), n, b, pm)
                rhs = t1_terminal(list(B.edges()), Bv, r, k, pm)
                stats["choices"] += 1
                key = ("both" if lhs and rhs else "neither" if not lhs and not rhs
                       else "lhs_only" if lhs else "rhs_only")
                stats[key] += 1
                if key in ("lhs_only", "rhs_only"):
                    print("DISAGREE", key, list(J.edges()), r, w, pm, flush=True)
                anybase |= lhs
            stats["base_root"] += int(anybase)
            if t1 and dc and not anybase:
                stats["t1_no_base"] += 1
                print("T1 but no base for any data:", list(J.edges()), "r", r,
                      "kappa", nx.node_connectivity(J), flush=True)
    print("ATLAS7", stats, flush=True)


if __name__ == "__main__" and sys.argv[1] == "atlas":
    check_atlas()

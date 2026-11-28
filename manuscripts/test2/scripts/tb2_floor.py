"""tb2_floor.py: the floor lift for (T2) (test2 session).

Setting: J with exactly two even vertices z, r, adjacent; B = J - z, of odd order n - 1, whose even
vertices are exactly N(z) - r.  Data: w in N(z) - r and a forest Phi of B whose odd-degree vertices
are exactly T' = N(z) - {r, w} (a T'-join), rooted with w a root of its component.  In B - Phi the
only even vertex is w.  Base: a Lovasz decomposition D0 of B - Phi with
   (i) p(v) not in V(Q0(v)) for every non-root v,  (ii) siblings on distinct paths.
Lift: append the parent edges at the child ends (forest stepping).  This gives a decomposition of B
into (n-2)/2 paths: the FLOOR for B.  Then one split at r gives at most n/2 paths with at least three
ends at r, i.e. (T2).  Every base found is checked, lifted, and both conclusions verified here.

Matching case (Phi a perfect matching of J[T']): the base is Conjecture DL (DisjL1) for the pairs of
the matching in the one-even graph B - Phi.  DL's exception is a pair of universal twins of its
component; it is recorded.

Modes:
  inst  : per instance, the first base over all data (matchings first, then spanning-tree T-joins,
          then every forest T-join up to cycle-space dimension XDIM); prints the tier.
  data  : per matching data (w, M0), whether a base exists (every orientation, exact), and whether
          some pair is a universal-twin pair of its component.
usage: python3 tb2_floor.py ORACLE MODE < instances
"""
import itertools
import random
import sys
from collections import Counter

import networkx as nx

from tb2 import Oracle, bfs_tree, norm, parse_paths, perfect_matchings, random_tree, \
    tjoin_in_tree, verify_test2

XDIM = 14


def floor_graph(J, z, phi):
    G = J.copy()
    G.remove_edges_from([(z, v) for v in list(J[z])])
    G.remove_edges_from(phi)
    return G  # z isolated


def rootings_w(phi, w, cap):
    F = nx.Graph(list(phi))
    comps = [sorted(c) for c in nx.connected_components(F)]
    choices = [[w] if w in c else c for c in comps]
    out = []
    for roots in itertools.product(*choices):
        par, order = {}, []
        for c, ro in zip(comps, roots):
            seen = {ro}
            q = [ro]
            for u in q:
                for v in sorted(F[u]):
                    if v not in seen:
                        seen.add(v)
                        par[v] = u
                        order.append(v)
                        q.append(v)
        out.append((par, order))
        if len(out) >= cap:
            break
    return out


def qline(G, n, par):
    E = list(G.edges())
    b = [G.degree(v) % 2 for v in range(n)]
    masks = [(1 << v) | ((1 << par[v]) if v in par else 0) for v in range(n)]
    return f"WC {n} {len(E)} " + " ".join(f"{u} {v}" for u, v in E) + " " + \
        " ".join(map(str, b)) + " " + " ".join(map(str, masks))


def check_and_lift(J, z, r, G, n, par, order, D0):
    used = set()
    ends = [0] * n
    for P in D0:
        assert len(P) >= 2 and len(set(P)) == len(P)
        for a, b in zip(P, P[1:]):
            assert G.has_edge(a, b)
            e = frozenset((a, b))
            assert e not in used
            used.add(e)
        ends[P[0]] += 1
        ends[P[-1]] += 1
    assert len(used) == G.number_of_edges()
    assert all(ends[v] == G.degree(v) % 2 for v in range(n))
    Q = {}
    for P in D0:
        Q[P[0]] = P
        Q[P[-1]] = P
    for v, p in par.items():
        assert p not in Q[v]
    for x in par:
        for y in par:
            if x < y and par[x] == par[y]:
                assert Q[x] is not Q[y]
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
    # floor: a decomposition of B = J - z with (n-2)/2 paths
    B = J.copy()
    B.remove_node(z)
    used = set()
    for P in paths:
        for a, b in zip(P, P[1:]):
            assert B.has_edge(a, b)
            used.add(frozenset((a, b)))
    assert len(used) == B.number_of_edges() and len(paths) <= (n - 2) // 2
    er = sum((P[0] == r) + (P[-1] == r) for P in paths)
    while er < 3:
        j = [j for j, P in enumerate(paths) if r in P[1:-1]][0]
        P = paths[j]
        k = P.index(r)
        paths[j:j + 1] = [P[:k + 1], P[k:]]
        er += 2
    verify_test2(J, z, r, paths)
    return True


def univ_twin(G, a, b):
    C = nx.node_connected_component(G, a)
    if b not in C:
        return False
    return set(G[a]) == set(G[b]) == set(C) - {a, b}


def matching_data(J, z, r):
    U = sorted(J[z])
    for w in U:
        if w == r:
            continue
        for pm in perfect_matchings([u for u in U if u not in (r, w)], J):
            yield w, pm


def decide(oracle, J, z, r, n, w, phi, cap=10 ** 6):
    G = floor_graph(J, z, phi)
    assert G.degree(w) % 2 == 0 and all(G.degree(v) % 2 == 1 for v in range(n) if v not in (w, z))
    for par, order in rootings_w(phi, w, cap):
        o = oracle.query(qline(G, n, par))
        assert o[0] in "01", o
        if o.startswith("1"):
            check_and_lift(J, z, r, G, n, par, order, parse_paths(o))
            return True
    return False


def forest_tjoins(B, T, xdim, rng, seen):
    """Spanning-tree T-joins first, then every forest T-join (cycle space) if dim <= xdim."""
    trees = [bfs_tree(B, s) for s in sorted(B)] + [random_tree(B, rng) for _ in range(20)]
    for S in trees:
        phi = tjoin_in_tree(S, T)
        if norm(phi) not in seen:
            seen.add(norm(phi))
            yield "S", phi
    E = sorted(tuple(sorted(e)) for e in B.edges())
    idx = {e: i for i, e in enumerate(E)}
    cyc = []
    for c in nx.cycle_basis(B):
        vec = 0
        for a, b in zip(c, c[1:] + c[:1]):
            vec ^= 1 << idx[tuple(sorted((a, b)))]
        cyc.append(vec)
    if len(cyc) > xdim:
        yield "UNDEC", None
        return
    phi0 = 0
    for e in tjoin_in_tree(bfs_tree(B, min(B)), T):
        phi0 |= 1 << idx[tuple(sorted(e))]
    for k in range(len(cyc) + 1):
        for comb in itertools.combinations(cyc, k):
            v = phi0
            for c in comb:
                v ^= c
            phi = [E[i] for i in range(len(E)) if v >> i & 1]
            if nx.is_forest(nx.Graph(phi)) and norm(phi) not in seen:
                seen.add(norm(phi))
                yield "X", phi


def main():
    oracle = Oracle(sys.argv[1])
    mode = sys.argv[2]
    rng = random.Random(1)
    stats = Counter()
    for line in sys.stdin:
        if not line.strip():
            continue
        g6, tail = line.split(None, 1)
        f = tail.split("|")[0].split()
        z, r = int(f[0]), int(f[1])
        J = nx.from_graph6_bytes(g6.encode())
        n = J.number_of_nodes()
        if mode == "data":
            for w, pm in matching_data(J, z, r):
                G = floor_graph(J, z, pm)
                tw = any(univ_twin(G, a, b) for a, b in pm)
                ok = decide(oracle, J, z, r, n, w, pm)
                stats[("base" if ok else "nobase", "twin" if tw else "notwin")] += 1
                if not ok:
                    print("NOBASE", g6, z, r, w, pm, "twin" if tw else "notwin", flush=True)
            continue
        # mode inst
        tier = None
        for w, pm in matching_data(J, z, r):
            if decide(oracle, J, z, r, n, w, pm):
                tier = "M"
                break
        if tier is None:
            B = J.copy()
            B.remove_node(z)
            seen = set()
            und = False
            for w in sorted(J[z]):
                if w == r or tier:
                    continue
                T = [u for u in J[z] if u not in (r, w)]
                for t, phi in forest_tjoins(B, T, XDIM, rng, seen):
                    if t == "UNDEC":
                        und = True
                        break
                    if decide(oracle, J, z, r, n, w, phi, cap=64 if t == "S" else 10 ** 6):
                        tier = t
                        break
            if tier is None:
                tier = "UNDEC" if und else "ABSENT"
        stats[tier] += 1
        print(g6, z, r, J.degree(z), J.degree(r), tier, flush=True)
    print("SUMMARY", dict(stats), file=sys.stderr)


if __name__ == "__main__":
    main()

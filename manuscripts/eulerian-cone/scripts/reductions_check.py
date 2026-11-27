"""reductions_check.py: executes the constructions of the reduction lemmas (eulerian-cone, Section 5)
on real decompositions and verifies every output (manuscript Section 5).

For every connected Eulerian graph B in the input files, every root r and every vertex v != r of
degree 2 with neighbours a, b:

  * SUPPRESS (Lemma 5.1): if ab is not an edge, take an optimal rooted decomposition of B/v
    (re.c), subdivide ab by v, and check that the result is a decomposition of B with the same
    number of paths and an end at r.
  * EAR (Lemma 5.2, Prop. 5.3): if ab is an edge and B' = B - v - ab is connected, take an optimal
    rooted decomposition D' of B', insert the triangle avb at a (or b), and check that the result
    has |D'| + 1 paths and the same number of ends as D' at every vertex of B'.
  * EAR-CUT (Prop. 5.4): if ab is an edge and B' is disconnected, glue rooted decompositions of the
    two components and check that the result has |D_a| + |D_b| paths (|D_b| + 1 if the component
    of a is {a}) and an end at r.
  * TWIN (Prop. 5.5): for a second degree-2 vertex u != r with N(u) = N(v) and B - u - v
    connected, insert the 4-cycle a u b v at a, and check |D''| + 1 paths and the same ends.
  * ROOT2 (Prop. 5.6): the root itself of degree 2 (suppress and split, or insert the ear with r last).
Checked in every case: partition into paths, size, end(s) at r.  Ends at every old vertex are checked
for EAR and TWIN.  The bound ceil(n/2) is checked where the manuscript claims it: SUPPRESS, EAR at odd
n, EAR-CUT, TWIN at even n, ROOT2 at odd n.

usage: python3 reductions_check.py RE_BINARY FILE.g6 ...
"""
import subprocess
import sys
from collections import Counter

import networkx as nx

RE = sys.argv[1]
cache = {}


def witness(G, r):
    """An optimal decomposition of G with an end at r (re.c -x), in G's labels."""
    nodes = sorted(G)
    idx = {v: i for i, v in enumerate(nodes)}
    H = nx.Graph()
    H.add_nodes_from(range(len(nodes)))  # graph6 follows this node order
    H.add_edges_from((idx[x], idx[y]) for x, y in G.edges())
    g6 = nx.to_graph6_bytes(H, header=False).decode().strip()
    key = (g6, idx[r])
    if key not in cache:
        out = subprocess.run([RE, "-x", "-r", str(idx[r])], input=g6 + "\n", capture_output=True,
                             text=True).stdout.strip()
        g, rest = out.split(None, 1)
        head, *paths = rest.split("|")
        f = head.split()
        assert f[3] in ("OK", "OVER"), out
        cache[key] = [list(map(int, p.split())) for p in paths if p.strip()]
    return [[nodes[i] for i in P] for P in cache[key]]


def check_decomp(G, D):
    used = set()
    ends = Counter()
    for P in D:
        assert len(P) >= 2 and len(set(P)) == len(P), P
        for x, y in zip(P, P[1:]):
            e = frozenset((x, y))
            assert G.has_edge(x, y) and e not in used, (P, x, y)
            used.add(e)
        ends[P[0]] += 1
        ends[P[-1]] += 1
    assert len(used) == G.number_of_edges()
    return ends


def ends_of(D):
    c = Counter()
    for P in D:
        c[P[0]] += 1
        c[P[-1]] += 1
    return c


def insert_cycle(D, a, chain, Gp):
    """Insert the cycle a - chain[0] - ... - chain[-1] - a, where chain[0] may be an old vertex b
    (for the triangle: chain = [b, v]; for the 4-cycle: chain = [u, b, v]) and chain[-1] is new.
    Returns a decomposition with one more path and unchanged ends at old vertices."""
    old = set(Gp)
    D = [list(P) for P in D]
    for j, Q in enumerate(D):
        if a in Q[1:-1]:
            i = Q.index(a)
            if any(x in old and x in Q[:i] for x in chain):
                Q = Q[::-1]
                i = Q.index(a)
            assert not any(x in Q[:i] for x in chain)
            D[j:j + 1] = [Q[:i + 1] + chain, [chain[-1]] + Q[i:]]
            return D
    for j, P in enumerate(D):
        if P[0] == a or P[-1] == a:
            if P[-1] == a:
                P = P[::-1]
            last = chain[-1]
            D[j:j + 1] = [[last] + P, [last] + chain[-2::-1] + [a]]
            return D
    raise AssertionError("a has no edge")


def suppress(B, v):
    a, b = list(B[v])
    H = B.copy()
    H.remove_node(v)
    H.add_edge(a, b)
    return H, a, b


def subdivide(D, a, b, v):
    out = []
    for P in D:
        Q = [P[0]]
        for x, y in zip(P, P[1:]):
            if {x, y} == {a, b}:
                Q.append(v)
            Q.append(y)
        out.append(Q)
    return out


def main():
    stats = Counter()
    for fn in sys.argv[2:]:
        for line in open(fn):
            B = nx.from_graph6_bytes(line.strip().encode())
            n = B.number_of_nodes()
            ce = (n + 1) // 2
            deg2 = [v for v in B if B.degree(v) == 2]
            for r in B:
                for v in deg2:
                    if v == r:
                        continue
                    a, b = list(B[v])
                    if not B.has_edge(a, b):
                        H, a, b = suppress(B, v)
                        Ds = witness(H, r)
                        D = subdivide(Ds, a, b, v)
                        e = check_decomp(B, D)
                        assert e[r] >= 1 and len(D) == len(Ds) <= ce
                        stats["SUPPRESS"] += 1
                        continue
                    Bp = B.copy()
                    Bp.remove_node(v)
                    Bp.remove_edge(a, b)
                    if nx.is_connected(Bp):
                        if Bp.degree(a) == 0:
                            a, b = b, a
                        Dp = witness(Bp, r)
                        D = insert_cycle(Dp, a, [b, v], Bp)
                        e = check_decomp(B, D)
                        e0 = ends_of(Dp)
                        assert len(D) == len(Dp) + 1
                        assert all(e[x] == e0[x] for x in Bp) and e[v] == 2
                        stats["EAR"] += 1
                        if n % 2 == 1:
                            assert len(D) <= ce
                            stats["EAR-odd-ok"] += 1
                        else:
                            stats["EAR-even-ok" if len(D) <= ce else "EAR-even-over"] += 1
                    else:
                        comps = list(nx.connected_components(Bp))
                        assert len(comps) == 2
                        Ca = next(c for c in comps if a in c)
                        Cb = next(c for c in comps if b in c)
                        if r in Cb:
                            a, b, Ca, Cb = b, a, Cb, Ca
                        Ba, Bb = B.subgraph(Ca).copy(), B.subgraph(Cb).copy()
                        Ba.remove_edges_from([(a, b)])
                        Bb.remove_edges_from([(a, b)])
                        if len(Cb) == 1:
                            # b has neighbours a, v only: a triangle hanging at a
                            Da = witness(Ba, r)
                            D = insert_cycle(Da, a, [b, v], Ba)
                            size_ok = len(D) == len(Da) + 1
                        elif len(Ca) == 1:
                            # a has neighbours b, v only (possibly a = r): insert b - v - a - b so
                            # that the new vertex a is the last vertex of the chain, an end twice
                            Db = witness(Bb, b)
                            D = insert_cycle(Db, b, [v, a], Bb)
                            size_ok = len(D) == len(Db) + 1
                        else:
                            Da = witness(Ba, r)
                            Db = witness(Bb, b)
                            Pb = next(P for P in Db if P[0] == b or P[-1] == b)
                            rest_b = [P for P in Db if P is not Pb]
                            if Pb[0] == b:
                                Pb = Pb[::-1]
                            Q = next((P for P in Da if a in P[1:-1]), None)
                            if Q is not None:
                                i = Q.index(a)
                                new = [Q[:i + 1] + [v, b], Pb + Q[i:]]
                                D = [P for P in Da if P is not Q] + rest_b + new
                            else:
                                Pa0 = next(P for P in Da if P[0] == a or P[-1] == a)
                                Pa = Pa0[::-1] if Pa0[-1] == a else Pa0
                                new = [Pb + Pa, [a, v, b]]
                                D = [P for P in Da if P is not Pa0] + rest_b + new
                            size_ok = len(D) == len(Da) + len(Db)
                        e = check_decomp(B, D)
                        assert size_ok and e[r] >= 1 and len(D) <= ce, (line, r, v)
                        stats["EAR-CUT"] += 1
                # the root itself of degree 2 (Prop. 5.6): suppress and split, or insert the
                # triangle with r as the last chain vertex
                if B.degree(r) == 2:
                    a, b = list(B[r])
                    if not B.has_edge(a, b):
                        H, a, b = suppress(B, r)
                        Ds = witness(H, a)
                        D = subdivide(Ds, a, b, r)
                        j = next(j for j, P in enumerate(D) if r in P[1:-1])
                        P = D[j]
                        i = P.index(r)
                        D[j:j + 1] = [P[:i + 1], P[i:]]
                        e = check_decomp(B, D)
                        assert e[r] == 2 and len(D) == len(Ds) + 1
                        if n % 2 == 1:
                            assert len(D) <= ce
                        stats["ROOT2-SUPPRESS"] += 1
                    else:
                        Bp = B.copy()
                        Bp.remove_node(r)
                        Bp.remove_edge(a, b)
                        if nx.is_connected(Bp):
                            if Bp.degree(a) == 0:
                                a, b = b, a
                            Dp = witness(Bp, a)
                            D = insert_cycle(Dp, a, [b, r], Bp)
                            e = check_decomp(B, D)
                            assert e[r] == 2 and len(D) == len(Dp) + 1
                            if n % 2 == 1:
                                assert len(D) <= ce
                            stats["ROOT2-EAR"] += 1
                        else:
                            stats["ROOT2-EAR-CUT-skip"] += 1
                # twins
                for i, u in enumerate(deg2):
                    for v in deg2[i + 1:]:
                        if r in (u, v) or set(B[u]) != set(B[v]):
                            continue
                        a, b = list(B[u])
                        Bpp = B.copy()
                        Bpp.remove_nodes_from([u, v])
                        if not nx.is_connected(Bpp) or Bpp.number_of_nodes() < 3:
                            stats["TWIN-skip"] += 1
                            continue
                        if Bpp.degree(a) == 0:
                            a, b = b, a
                        Dpp = witness(Bpp, r)
                        D = insert_cycle(Dpp, a, [u, b, v], Bpp)
                        e = check_decomp(B, D)
                        e0 = ends_of(Dpp)
                        assert len(D) == len(Dpp) + 1 and all(e[x] == e0[x] for x in Bpp)
                        if n % 2 == 0:
                            assert len(D) <= ce
                        stats["TWIN"] += 1
        print(fn, dict(stats), flush=True)


if __name__ == "__main__":
    main()

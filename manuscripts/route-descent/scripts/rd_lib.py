"""Route descent: shared library (oracle interface, witness checker, Thm 21 construction).

Graphs are networkx graphs on vertices 0..n-1.

* Oracle: tools/route_ext.c (compiled on first use into a temporary directory).
    realisable(G, b)               -- is the profile b realisable?
    ext(G, b, c, forbid)           -- is there a realisation of b whose path at c avoids `forbid`?
    witness(G, b[, c, forbid])     -- one realisation (list of vertex lists), checked independently.
* Construction (endpoint-min-max Thm 21, `thm:ps`):
    random forest T-join J of Ev (T-join of a random spanning tree), and, at each vertex v, a
    random pairing of the odd vertices of F^v by edge-disjoint paths of F^v.  The pairing is built
    greedily: remove any path of F^v between two odd vertices; the remaining graph still has its
    odd vertices pairable (every component has an even number of them), so the greedy procedure
    always completes, and every edge-disjoint pairing has positive probability when the paths are
    taken from random spanning trees.
"""
import os
import random
import subprocess
import tempfile
from itertools import product

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", "..", ".."))
TOOLS = os.path.join(ROOT, "tools")
_BIN = None
_PROC = None


def _oracle():
    global _BIN, _PROC
    if _PROC is None:
        d = tempfile.mkdtemp(prefix="route_ext_")
        _BIN = os.path.join(d, "route_ext")
        subprocess.run(["gcc", "-O2", "-o", _BIN, os.path.join(TOOLS, "route_ext.c")], check=True)
        _PROC = subprocess.Popen([_BIN], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    return _PROC


def _graph_str(G):
    n = G.number_of_nodes()
    E = list(G.edges())
    return f"{n} {len(E)} " + " ".join(f"{u} {v}" for u, v in E)


def _query(line):
    p = _oracle()
    p.stdin.write(line + "\n")
    p.stdin.flush()
    out = p.stdout.readline().strip()
    return out


# budgeted search: BUDGET = None means exhaustive; otherwise RESTARTS randomised attempts with
# BUDGET nodes each, then one exhaustive attempt if FINAL is set, else None (unknown).
BUDGET = None
RESTARTS = 8
FINAL = True


def _decide(tag, body):
    if BUDGET is None:
        r = _query(tag + " " + body)
        if r == "-1":
            raise ValueError("unsupported instance")
        return r.startswith("1")
    for s in range(RESTARTS):
        bud = BUDGET * (2 ** s)
        r = _query(tag + "B " + body + f" {s + 1} {bud}")
        if r == "-1":
            raise ValueError("unsupported instance")
        if r.startswith("1"):
            return True
        if r.startswith("0"):
            return False
    if FINAL:
        return _query(tag + " " + body).startswith("1")
    return None


def realisable(G, b):
    return _decide("P", _graph_str(G) + " " + " ".join(str(b[v]) for v in range(G.number_of_nodes())))


def ext(G, b, c, forbid):
    f = sum(1 << x for x in forbid)
    assert c not in forbid
    return _decide("X", _graph_str(G) + " " + " ".join(str(b[v]) for v in range(G.number_of_nodes()))
                   + f" {c} {f}")


def witness(G, b, c=None, forbid=()):
    if c is None:
        line = "WP " + _graph_str(G) + " " + " ".join(str(b[v]) for v in range(G.number_of_nodes()))
    else:
        f = sum(1 << x for x in forbid)
        line = ("WX " + _graph_str(G) + " " + " ".join(str(b[v]) for v in range(G.number_of_nodes()))
                + f" {c} {f}")
    r = _query(line)
    if not r.startswith("1"):
        return None
    parts = r.split("|")[1:-1]
    paths = [list(map(int, s.split())) for s in parts]
    check_partition(G, b, paths)
    if c is not None:
        q = [P for P in paths if c in (P[0], P[-1])]
        assert any(not (set(P) & set(forbid)) for P in q), "constraint not met"
    return paths


def check_partition(G, b, paths):
    """Independent check that `paths` partition E(G) into simple paths with b(v) ends at v."""
    seen = set()
    ends = [0] * G.number_of_nodes()
    for P in paths:
        assert len(P) >= 2 and len(set(P)) == len(P), "not a simple path"
        for x, y in zip(P, P[1:]):
            assert G.has_edge(x, y), "non-edge"
            e = frozenset((x, y))
            assert e not in seen, "edge used twice"
            seen.add(e)
        ends[P[0]] += 1
        ends[P[-1]] += 1
    assert len(seen) == G.number_of_edges(), "edges not covered"
    assert all(ends[v] == b[v] for v in range(G.number_of_nodes())), "wrong profile"


# ---------------------------------------------------------------------------------------------
# graph basics

def even_vertices(G):
    return [v for v in G if G.degree(v) % 2 == 0 and G.degree(v) > 0]


def simple_profile(G, S):
    S = set(S)
    return [1 if G.degree(v) % 2 else (2 if v in S else 0) for v in range(G.number_of_nodes())]


def relabel(G):
    return nx.convert_node_labels_to_integers(G)


def from_g6(s):
    return relabel(nx.from_graph6_bytes(s.encode()))


# ---------------------------------------------------------------------------------------------
# Theorem 21 construction

def random_spanning_tree(G, rng):
    H = nx.Graph()
    H.add_nodes_from(G)
    for u, w in G.edges():
        H.add_edge(u, w, weight=rng.random())
    return nx.minimum_spanning_tree(H)


def tree_tjoin(S, T):
    """The unique T-join of the forest S."""
    T = set(T)
    J = set()
    for comp in nx.connected_components(S):
        root = next(iter(comp))
        order = list(nx.dfs_preorder_nodes(S, root))
        parent = {root: None}
        for u in order:
            for w in S[u]:
                if w not in parent:
                    parent[w] = u
        below = {u: (u in T) for u in comp}
        for u in reversed(order):
            if parent[u] is not None:
                if below[u]:
                    J.add(frozenset((u, parent[u])))
                below[parent[u]] ^= below[u]
    return J


def random_odd_pairing(H, rng):
    """Pair the odd vertices of H by edge-disjoint paths, choosing paths at random.
    Returns a list of (x, y, path)."""
    H = nx.Graph(H)
    out = []
    while True:
        odd = [x for x in H if H.degree(x) % 2]
        if not odd:
            return out
        x = rng.choice(odd)
        comp = nx.node_connected_component(H, x)
        S = random_spanning_tree(H.subgraph(comp), rng)
        ys = [y for y in odd if y in comp and y != x]
        y = rng.choice(ys)
        P = nx.shortest_path(S, x, y)
        H.remove_edges_from(zip(P, P[1:]))
        out.append((x, y, P))


def free_graph_at(G, F, v):
    Fv = nx.Graph(F)
    Fv.remove_edges_from([(v, x) for x in list(Fv[v])])
    Fv.add_edges_from((v, w) for w in G if w != v and not G.has_edge(v, w))
    return Fv


def construct(G, J, rng, deterministic=False):
    """Thm 21: transitions at each vertex from an edge-disjoint pairing of the odd vertices of F^v.
    Returns (pairs, routes, links) where routes[i] is the vertex list of the i-th route (from
    pairs[i][0] to pairs[i][1]) and links[v] is the list of (x, y, path) linking paths at v."""
    F = nx.Graph()
    F.add_nodes_from(G)
    F.add_edges_from(e for e in G.edges() if frozenset(e) not in J)
    trans = {}
    links = {}
    for v in G:
        NJ = [x for x in G[v] if frozenset((v, x)) in J]
        if not NJ:
            continue
        Fv = free_graph_at(G, F, v)
        odd = {x for x in Fv if Fv.degree(x) % 2}
        assert odd == set(NJ) | ({v} if G.degree(v) % 2 == 0 else set()), "parity claim fails"
        pr = random_odd_pairing(Fv, rng)
        links[v] = pr
        for a, c, _ in pr:
            if a == v:
                trans[(v, c)] = None
            elif c == v:
                trans[(v, a)] = None
            else:
                trans[(v, a)] = c
                trans[(v, c)] = a
    Ev = even_vertices(G)
    routes, used = [], set()
    done = set()
    for s in Ev:
        if s in done:
            continue
        x = next(x for x in G[s] if frozenset((s, x)) in J and trans.get((s, x), 0) is None)
        path, prev, cur = [s], s, x
        while True:
            path.append(cur)
            nxt = trans[(cur, prev)]
            if nxt is None:
                break
            prev, cur = cur, nxt
        E = {frozenset((path[i], path[i + 1])) for i in range(len(path) - 1)}
        assert len(set(path)) == len(path) and not (E & used), "routes are not edge-disjoint paths"
        used |= E
        routes.append(path)
        done.add(path[0])
        done.add(path[-1])
    assert used == J
    return [(r[0], r[-1]) for r in routes], routes, links


def min_tjoin(G, T, rng):
    """A minimum-cardinality T-join (a forest), chosen at random among minimum ones by
    perturbing unit weights by less than 1/|E| in total: min-weight perfect matching on T for the
    perturbed shortest-path metric, then the symmetric difference of the matched paths."""
    T = list(T)
    if not T:
        return set()
    m = G.number_of_edges()
    H = nx.Graph()
    for u, w in G.edges():
        H.add_edge(u, w, weight=1.0 + rng.random() / (2.0 * m + 2))
    dist, paths = {}, {}
    for s in T:
        d, p = nx.single_source_dijkstra(H, s)
        dist[s], paths[s] = d, p
    K = nx.Graph()
    for i, s in enumerate(T):
        for t in T[i + 1:]:
            K.add_edge(s, t, weight=-dist[s][t])
    mt = nx.max_weight_matching(K, maxcardinality=True)
    J = set()
    for s, t in mt:
        P = paths[s][t]
        for e in zip(P, P[1:]):
            J ^= {frozenset(e)}
    F = nx.Graph([tuple(e) for e in J])
    assert nx.is_forest(F)
    assert len(J) == min_tjoin_size(G, T)
    return J


def min_tjoin_size(G, T):
    T = list(T)
    d = dict(nx.all_pairs_shortest_path_length(G))
    K = nx.Graph()
    for i, s in enumerate(T):
        for t in T[i + 1:]:
            K.add_edge(s, t, weight=-d[s][t])
    mt = nx.max_weight_matching(K, maxcardinality=True)
    return sum(d[s][t] for s, t in mt)


def random_construction(G, rng, tjoin="tree"):
    if tjoin == "min":
        J = min_tjoin(G, even_vertices(G), rng)
    else:
        S = random_spanning_tree(G, rng)
        J = tree_tjoin(S, even_vertices(G))
    return construct(G, J, rng)


def transversals(pairs):
    for bits in product((0, 1), repeat=len(pairs)):
        yield tuple(p[i] for p, i in zip(pairs, bits))


def delete_route(G, route):
    H = nx.Graph(G)
    H.remove_edges_from(zip(route, route[1:]))
    return H


# ---------------------------------------------------------------------------------------------
# route-respecting realisations

def route_respecting(G, routes, M, want=False):
    """Is there a realisation of b_M in G in which every route R_p is a terminal segment (at its
    marked end) of some path?  Equivalently: a partition of F = G - J into paths with one end at
    every vertex such that appending every route at its unmarked end gives paths.  Returns the
    realisation of G (checked) if want=True, else a bool."""
    Mset = set(M)
    n = G.number_of_nodes()
    J = {frozenset(e) for r in routes for e in zip(r, r[1:])}
    F = nx.Graph()
    F.add_nodes_from(range(n))
    F.add_edges_from(e for e in G.edges() if frozenset(e) not in J)
    b = [F.degree(v) % 2 for v in range(n)]
    assert all(b) or n == 0
    crv = [1 << v for v in range(n)]
    tail_route = {}
    for R in routes:
        c = R[0] if R[-1] in Mset else R[-1]
        assert (R[0] in Mset) != (R[-1] in Mset)
        crv[c] = sum(1 << x for x in R)
        tail_route[c] = R if R[0] == c else R[::-1]
    body = _graph_str(F) + " " + " ".join(map(str, b)) + " " + " ".join(map(str, crv))
    if not want:
        return _decide("C", body)
    if BUDGET is None:
        r = _query("WC " + body)
    else:
        r = "2"
        for s in range(RESTARTS):
            r = _query("WCB " + body + f" {s + 1} {BUDGET * 2 ** s}")
            if r[0] in "01":
                break
        if r[0] == "2" and FINAL:
            r = _query("WC " + body)
    if r == "-1":
        raise ValueError("unsupported instance")
    if not r.startswith("1"):
        return None
    parts = [list(map(int, s.split())) for s in r.split("|")[1:-1]]
    check_partition(F, b, parts)
    out = []
    for Q in parts:
        P = list(Q)
        if P[0] in tail_route:
            P = tail_route[P[0]][::-1] + P[1:]
        if P[-1] in tail_route:
            P = P[:-1] + tail_route[P[-1]]
        out.append(P)
    check_partition(G, simple_profile(G, Mset), out)
    return out


def avoid(G, b, X):
    """Is b realisable by paths each avoiding X[s] and X[w] (s, w its ends)?  X: dict v -> set."""
    n = G.number_of_nodes()
    xs = [sum(1 << x for x in X.get(v, ())) & ~(1 << v) for v in range(n)]
    return _decide("A", _graph_str(G) + " " + " ".join(str(b[v]) for v in range(n)) + " "
                   + " ".join(map(str, xs)))


def sep(G, b, s1, s2=None):
    """Is b realisable by paths none of which contains both s1 and s2?  With s2 None, s1 is a
    list of pairs, none of which may lie on a common path."""
    n = G.number_of_nodes()
    prs = [(s1, s2)] if s2 is not None else list(s1)
    return _decide("S", _graph_str(G) + " " + " ".join(str(b[v]) for v in range(n)) + f" {len(prs)} "
                   + " ".join(f"{x} {y}" for x, y in prs))


def route_respecting_all(G, routes):
    """RR*: one partition of F = G - J into paths with one end at every vertex such that every
    route can be appended at EITHER end: a path with an end at a route end e meets that route only
    in e, and a path with ends e, e' at route ends has the two routes vertex-disjoint (so it is not
    a path joining the two ends of one route).  Then every transversal is realised at once."""
    n = G.number_of_nodes()
    J = {frozenset(e) for r in routes for e in zip(r, r[1:])}
    F = nx.Graph()
    F.add_nodes_from(range(n))
    F.add_edges_from(e for e in G.edges() if frozenset(e) not in J)
    b = [F.degree(v) % 2 for v in range(n)]
    crv = [1 << v for v in range(n)]
    for R in routes:
        m = sum(1 << x for x in R)
        crv[R[0]] = m
        crv[R[-1]] = m
    return _decide("C", _graph_str(F) + " " + " ".join(map(str, b)) + " " + " ".join(map(str, crv)))

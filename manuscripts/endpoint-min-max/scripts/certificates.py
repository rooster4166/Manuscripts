"""Proof certificates for pairing selection (PS), independent of the cut enumeration.

The Guarded Route Lemma of the manuscript says: if the even vertices are paired by edge-disjoint
paths ("routes") of G, and every passage x-v-y of a route through a vertex v lying on two or more
routes is guarded, then every half-set with one end of each pair marked is cut-feasible.
A passage is guarded by
  (a) a bypass: a vertex u != v, not an end of another passage through v, with xu, yu edges of G
      on no route; or
  (b) private neighbours: vertices w_x, w_y not adjacent to v (and != v) with x w_x, y w_y edges of G
      on no route, all private neighbours used at v being distinct.
A route system with no vertex on two routes (a linkage) needs no guards.

For every graph the script searches, in this order, for (1) a Hamiltonian path (pair consecutive
even vertices along it: a linkage), (2) any linkage, (3) a guarded route system.  It prints how many
graphs are certified by each step and lists the graphs with no certificate.  Every certified pairing
is also checked against the enumeration of tools/cutfeas.c, which tests the lemma itself.

Usage: python3 certificates.py [6] [8] [10] [bottleneck] [trees] [stress]
"""
import collections
import sys
import time

import networkx as nx

import emm_lib as L
from cut_selection import pairings


def hamiltonian_path(G):
    n = G.number_of_nodes()
    order = sorted(G, key=G.degree)

    def dfs(path, seen):
        if len(path) == n:
            return list(path)
        for y in G[path[-1]]:
            if y not in seen:
                seen.add(y)
                path.append(y)
                r = dfs(path, seen)
                if r:
                    return r
                path.pop()
                seen.discard(y)
        return None

    for s in order:
        r = dfs([s], {s})
        if r:
            return r
    return None


def vertex_paths(G, a, c, blocked):
    out = []

    def dfs(x, seen):
        if x == c:
            out.append(frozenset(seen))
            return
        for y in G[x]:
            if y not in seen and (y not in blocked or y == c):
                seen.add(y)
                dfs(y, seen)
                seen.discard(y)

    dfs(a, {a})
    return out


def linkable(G, P, used=frozenset()):
    if not P:
        return True
    (a, c), rest = P[0], P[1:]
    others = {x for q in rest for x in q}
    return any(linkable(G, rest, used | R) for R in vertex_paths(G, a, c, used | others))


def edge_paths(G, a, c, usedE):
    out = []

    def dfs(x, path, seen):
        if x == c:
            out.append(list(path))
            return
        for y in G[x]:
            if y not in seen and frozenset((x, y)) not in usedE:
                seen.add(y)
                path.append(y)
                dfs(y, path, seen)
                path.pop()
                seen.discard(y)

    dfs(a, [a], {a})
    return out


def guarded(G, routes):
    J = {frozenset((p[i], p[i + 1])) for p in routes for i in range(len(p) - 1)}
    on = collections.Counter(v for p in routes for v in p)
    passages = collections.defaultdict(list)
    for p in routes:
        for i in range(1, len(p) - 1):
            passages[p[i]].append((p[i - 1], p[i + 1]))

    def free(a, b):
        return G.has_edge(a, b) and frozenset((a, b)) not in J

    for v, ps in passages.items():
        if on[v] < 2:
            continue
        ends = []
        for (x, y) in ps:
            other = {w for q in ps if q != (x, y) for w in q}
            if any(u != v and u not in other and free(x, u) and free(y, u) for u in G):
                continue
            ends += [x, y]
        cands = [[w for w in G if w != v and not G.has_edge(w, v) and free(z, w)] for z in ends]

        def sdr(i, used):
            return i == len(ends) or any(sdr(i + 1, used | {w}) for w in cands[i] if w not in used)

        if not sdr(0, frozenset()):
            return False
    return True


def guarded_search(G, P, usedE=frozenset(), routes=()):
    if not P:
        return guarded(G, list(routes))  # noqa: the caller records P
    (a, c), rest = P[0], P[1:]
    for R in edge_paths(G, a, c, usedE):
        E = {frozenset((R[i], R[i + 1])) for i in range(len(R) - 1)}
        if guarded_search(G, rest, usedE | E, routes + (R,)):
            return True
    return False


def certify(G):
    """Return (kind, pairing) for the first certificate found, or (None, None)."""
    Ev = L.even_vertices(G)
    H = hamiltonian_path(G)
    if H:
        ev = [v for v in H if v in set(Ev)]
        return "hamiltonian path", [(ev[i], ev[i + 1]) for i in range(0, len(ev), 2)]
    for P in pairings(Ev):
        if linkable(G, P):
            return "linkage", P
    for P in pairings(Ev):
        if guarded_search(G, P):
            return "guarded routes", P
    return None, None


def good(P, F):
    return all(frozenset(q[o >> i & 1] for i, q in enumerate(P)) in F for o in range(1 << len(P)))


def run(name, graphs):
    """Certify every graph, and check each certified pairing against the cut enumeration
    (a test of the Guarded Route Lemma itself)."""
    t = time.time()
    c = collections.Counter()
    for G, F in zip(graphs, L.cut_feasible(graphs)):
        how, P = certify(G)
        c[how] += 1
        if how is None:
            print("   NO CERTIFICATE:", sorted(G.edges()), flush=True)
        elif not good(P, F):
            print("   LEMMA VIOLATED (certified pairing not good):", how, P, sorted(G.edges()), flush=True)
            c["lemma violated"] += 1
    print(f"{name}: {len(graphs)} graphs, {dict(c)}   [{time.time() - t:.0f}s]", flush=True)


def stress(count=400, tries=40, seed=3):
    """Random pairings with random edge-disjoint route systems on random graphs of order 8 and 10:
    every guarded system must give a good pairing (a direct test of the lemma)."""
    import random
    rng = random.Random(seed)
    stats = collections.Counter()

    def random_routes(G, P):
        used, routes = set(), []
        for a, c in P:
            ok = False
            for _ in range(20):
                path, seen, x = [a], {a}, a
                while x != c:
                    nb = [y for y in G[x] if y not in seen and frozenset((x, y)) not in used]
                    if not nb:
                        break
                    x = rng.choice(nb)
                    path.append(x)
                    seen.add(x)
                if x == c:
                    ok = True
                    break
            if not ok:
                return None
            used |= {frozenset((path[i], path[i + 1])) for i in range(len(path) - 1)}
            routes.append(path)
        return routes

    graphs = []
    while len(graphs) < count:
        n = rng.choice([8, 10])
        G = nx.gnp_random_graph(n, rng.choice([.25, .35, .5, .7]), seed=rng.randrange(2**31))
        if nx.is_connected(G) and len(L.even_vertices(G)) >= 4:
            graphs.append(G)
    for G, F in zip(graphs, L.cut_feasible(graphs)):
        Ev = L.even_vertices(G)
        for _ in range(tries):
            E = Ev[:]
            rng.shuffle(E)
            P = [(E[i], E[i + 1]) for i in range(0, len(E), 2)]
            R = random_routes(G, P)
            if R is None:
                continue
            on = collections.Counter(v for p in R for v in p)
            busy = any(c >= 2 for c in on.values())
            if guarded(G, R):
                stats["guarded with a busy vertex" if busy else "linkage"] += 1
                if not good(P, F):
                    stats["LEMMA VIOLATED"] += 1
                    print("   LEMMA VIOLATED:", sorted(G.edges()), R, flush=True)
            else:
                stats["unguarded, good" if good(P, F) else "unguarded, not good"] += 1
    print(f"stress test (seed {seed}): {dict(stats)}", flush=True)


def main():
    for w in sys.argv[1:] or ["6", "8", "10", "bottleneck", "trees", "stress"]:
        if w == "stress":
            stress()
        elif w == "trees":
            for n in (8, 10, 12):
                run(f"trees, order {n}", [T for T in (L.relabel(T) for T in nx.nonisomorphic_trees(n))
                                         if len(L.even_vertices(T)) >= 2])
        elif w in ("6", "8"):
            run(f"all connected, order {w}", L.all_connected(int(w)))
        elif w == "10":
            run("random G(10,p), seed 20261127", L.random_sample())
        elif w == "bottleneck":
            run("bottleneck families, orders 6-10", L.bottleneck())


if __name__ == "__main__":
    main()

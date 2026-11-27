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
graphs are certified by each step and lists the graphs with no certificate.

Usage: python3 certificates.py [6] [8] [10] [bottleneck]
"""
import collections
import sys
import time

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
        return guarded(G, list(routes))
    (a, c), rest = P[0], P[1:]
    for R in edge_paths(G, a, c, usedE):
        E = {frozenset((R[i], R[i + 1])) for i in range(len(R) - 1)}
        if guarded_search(G, rest, usedE | E, routes + (R,)):
            return True
    return False


def certify(G):
    Ev = L.even_vertices(G)
    if hamiltonian_path(G):
        return "hamiltonian path"
    if any(linkable(G, P) for P in pairings(Ev)):
        return "linkage"
    if any(guarded_search(G, P) for P in pairings(Ev)):
        return "guarded routes"
    return None


def run(name, graphs):
    t = time.time()
    c = collections.Counter()
    for G in graphs:
        how = certify(G)
        c[how] += 1
        if how is None:
            print("   NO CERTIFICATE:", sorted(G.edges()), flush=True)
    print(f"{name}: {len(graphs)} graphs, {dict(c)}   [{time.time() - t:.0f}s]", flush=True)


def main():
    for w in sys.argv[1:] or ["6", "8", "10", "bottleneck"]:
        if w in ("6", "8"):
            run(f"all connected, order {w}", L.all_connected(int(w)))
        elif w == "10":
            run("random G(10,p), seed 20261127", L.random_sample())
        elif w == "bottleneck":
            run("bottleneck families, orders 6-10", L.bottleneck())


if __name__ == "__main__":
    main()

"""RR and realisability for minimum T-joins with ARBITRARY (unlinked) transitions.

For a minimum T-join J of Ev, choose at every vertex a random pairing of its J-edges (leaving one
unpaired at even vertices); since J is a forest this decomposes J into routes pairing Ev.  Check every
transversal: realisable? route-respecting?  Also check whether the pairing satisfies the linked
transitions condition (by trying random T-join pairings of F^v that realise it).

Usage: python3 unlinked.py n count budget
"""
import random
import sys

import networkx as nx

import families
import rd_lib as L


def random_routes(G, J, rng):
    inc = {v: [] for v in G}
    for e in J:
        a, b = tuple(e)
        inc[a].append(b)
        inc[b].append(a)
    trans = {}
    for v, nb in inc.items():
        nb = nb[:]
        rng.shuffle(nb)
        if len(nb) % 2:
            trans[(v, nb.pop())] = None
        while nb:
            x, y = nb.pop(), nb.pop()
            trans[(v, x)] = y
            trans[(v, y)] = x
    routes, done = [], set()
    for s in L.even_vertices(G):
        if s in done:
            continue
        x = next(x for x in inc[s] if trans[(s, x)] is None)
        path, prev, cur = [s], s, x
        while True:
            path.append(cur)
            nxt = trans[(cur, prev)]
            if nxt is None:
                break
            prev, cur = cur, nxt
        routes.append(path)
        done |= {path[0], path[-1]}
    return routes


def main():
    n, count, L.BUDGET = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    L.FINAL = False
    rng = random.Random(5)
    tot = notreal = rrfail = rrunk = 0
    for G in families.random_graphs(n, count, 77 + n, 0.15, 0.45):
        J = L.min_tjoin(G, L.even_vertices(G), rng)
        routes = random_routes(G, J, rng)
        pairs = [(r[0], r[-1]) for r in routes]
        for M in list(L.transversals(pairs))[:32]:
            tot += 1
            rr = L.route_respecting(G, routes, M)
            if rr is None:
                rrunk += 1
                rb = L.realisable(G, L.simple_profile(G, M))
                if rb is False:
                    notreal += 1
                    print("NOT REALISABLE (unlinked)", sorted(G.edges()), routes, M, flush=True)
            elif not rr:
                rrfail += 1
                rb = L.realisable(G, L.simple_profile(G, M))
                if rb is False:
                    notreal += 1
                    print("NOT REALISABLE (unlinked)", sorted(G.edges()), routes, M, flush=True)
    print(f"n={n}: {tot} transversals of unlinked min-T-join route systems; RR false {rrfail}, "
          f"RR undecided {rrunk}, not realisable {notreal}")


if __name__ == "__main__":
    main()

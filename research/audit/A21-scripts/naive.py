"""naive.py -- audit A21: naive enumeration of ALL Lovasz decompositions of a small graph.

Enumerates the full product, over vertices, of the pairings of incident edges that leave exactly
d(v) mod 2 edges unpaired; traces the trails; keeps the transition systems whose trails are all
paths (no closed trail, no repeated vertex).  No pruning, so only for tiny graphs (n <= 5 or
sparse n = 7).  Used to cross-check ts.c and to verify Proposition 3.1 by exhaustion.

lovasz_decomps(n, edges) -> list of decompositions, each a list of vertex sequences.
"""
import itertools


def pairings(items, unpaired):
    """All ways to pair `items` leaving exactly `unpaired` (0 or 1) unpaired. Yields (pairs, singles)."""
    items = list(items)
    if not items:
        if unpaired == 0:
            yield [], []
        return
    first, rest = items[0], items[1:]
    if unpaired == 1:
        for p, s in pairings(rest, 0):
            yield p, [first] + s
    for i, other in enumerate(rest):
        for p, s in pairings(rest[:i] + rest[i + 1:], unpaired):
            yield [(first, other)] + p, s


def lovasz_decomps(n, edges):
    edges = [tuple(e) for e in edges]
    inc = {v: [i for i, e in enumerate(edges) if v in e] for v in range(n)}
    per_vertex = [list(pairings(inc[v], len(inc[v]) % 2)) for v in range(n)]
    out = []
    for choice in itertools.product(*per_vertex):
        # partner[(e, v)] = edge paired with e at v, or None if e ends at v
        partner = {}
        for v, (pairs, singles) in zip(range(n), choice):
            for a, b in pairs:
                partner[(a, v)] = b
                partner[(b, v)] = a
            for a in singles:
                partner[(a, v)] = None
        seen = set()
        paths = []
        ok = True
        # trails start at an end: an edge-end with partner None
        for (e, v), p in partner.items():
            if p is not None or e in seen:
                continue
            seq = [v]
            cur_e, cur_v = e, v
            while True:
                seen.add(cur_e)
                a, b = edges[cur_e]
                w = b if a == cur_v else a
                seq.append(w)
                nxt = partner[(cur_e, w)]
                if nxt is None:
                    break
                cur_e, cur_v = nxt, w
            if len(set(seq)) != len(seq):
                ok = False
                break
            paths.append(seq)
        if ok and len(seen) != len(edges):  # some edges lie on closed trails
            ok = False
        if ok:
            out.append(paths)
    return out


def terminal_pairs(decomp):
    """Set of (x, y) such that some path ends at x with last edge xy."""
    s = set()
    for P in decomp:
        s.add((P[0], P[1]))
        s.add((P[-1], P[-2]))
    return s


if __name__ == "__main__":
    # Proposition 3.1 example: x,t,z,y,p = 0,1,2,3,4; edges xt,xz,xy,tz,ty,yp
    E = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (3, 4)]
    D = lovasz_decomps(5, E)
    print("Prop 3.1 example: number of Lovasz decompositions =", len(D))
    T = set().union(*(terminal_pairs(d) for d in D))
    print("  xy=(0,3) terminal at x in some decomposition:", (0, 3) in T)
    print("  yx=(3,0) terminal at y in some decomposition:", (3, 0) in T)
    for d in D:
        print("   ", d)

"""Independent brute-force check of the stl oracle on small graphs.

Enumerates every path decomposition of J with a given end profile (simple recursion: the
lowest remaining edge lies on some path; enumerate all paths through it), classifies the
transitions at z, and compares with tools/stl.c on: ST-any, STL(r), BAL(r), for every
connected graph of odd order n <= 7 with exactly one even vertex.
"""
import sys, itertools
import networkx as nx
from common import Oracle, even_vertices, relabel


def paths_through_edge(adj, rem, e):
    u, v = e
    # all simple paths in the graph `rem` (set of frozenset edges) containing edge uv:
    # extend from v away from u and from u away from v
    def ext(path, vis):
        yield path
        c = path[-1]
        for w in adj[c]:
            f = frozenset((c, w))
            if w not in vis and f in rem:
                yield from ext(path + [w], vis | {w})
    rem2 = rem - {frozenset(e)}
    for left in ext([u], {u, v}):
        # left: u ... going away from v; need edges in rem2 (not using uv)
        pass
    # simpler: generate tails from u (not via v) and from v (not via u), disjoint
    def tails(start, banned, R):
        out = []
        def go(path, vis):
            out.append(path)
            c = path[-1]
            for w in adj[c]:
                f = frozenset((c, w))
                if w not in vis and f in R:
                    go(path + [w], vis | {w})
        go([start], {start} | banned)
        return out
    for tu in tails(u, {v}, rem2):
        used = set(frozenset((tu[i], tu[i + 1])) for i in range(len(tu) - 1))
        for tv in tails(v, set(tu), rem2 - used):
            yield list(reversed(tu)) + tv


def all_decomps(G, prof):
    adj = {v: list(G[v]) for v in G}
    edges = sorted(frozenset(e) for e in G.edges())
    order = {e: i for i, e in enumerate(sorted(edges, key=lambda f: tuple(sorted(f))))}
    res = []

    def rec(rem, ends, acc):
        if not rem:
            if all(ends[v] == prof[v] for v in G):
                res.append(list(acc))
            return
        e = min(rem, key=lambda f: order[f])
        e = tuple(sorted(e))
        for P in paths_through_edge(adj, rem, e):
            a, b = P[0], P[-1]
            if ends[a] + 1 > prof[a] or ends[b] + 1 > prof[b]:
                continue
            used = set(frozenset((P[i], P[i + 1])) for i in range(len(P) - 1))
            ends[a] += 1; ends[b] += 1
            acc.append(P)
            rec(rem - used, ends, acc)
            acc.pop()
            ends[a] -= 1; ends[b] -= 1

    rec(frozenset(edges), {v: 0 for v in G}, [])
    return res


def classify(D, z, r):
    LL = SS = 0; rs = 0
    for P in D:
        if z not in P:
            continue
        k = P.index(z); L = len(P) - 1
        sa, sb = (k == 1), (L - k == 1)
        if sa and sb: SS += 1
        if not sa and not sb: LL += 1
        if r is not None and ((sa and P[0] == r) or (sb and P[-1] == r)):
            rs = 1
    return LL, SS, rs


def main(nmax=7):
    orc = Oracle()
    tested = 0; mism = 0
    for n in range(3, nmax + 1, 2):
        gs = [relabel(nx.from_graph6_bytes(l.strip())) for l in open(f'../../../data/conn{n}.g6', 'rb')] if n >= 4 else [nx.path_graph(3)]
        for G in gs:
            ev = even_vertices(G)
            if len(ev) != 1:
                continue
            z = ev[0]
            prof = {v: G.degree(v) % 2 for v in G}
            D_all = all_decomps(G, prof)
            assert D_all, 'Lovasz fails?!'
            cls = [classify(D, z, None) for D in D_all]
            st_any = any(LL == 0 for LL, SS, rs in cls)
            got = orc.query(G, prof, z, -1, 1, 99)
            tested += 1
            if got != int(st_any):
                mism += 1; print('MISMATCH st_any', nx.to_graph6_bytes(G, header=False), got, st_any)
            for r in G[z]:
                cr = [classify(D, z, r) for D in D_all]
                stl = any(LL == 0 and SS >= rs for LL, SS, rs in cr)
                bal = any(LL - SS + rs <= 0 for LL, SS, rs in cr)
                g1 = orc.query(G, prof, z, r, 1, 0)
                g2 = orc.query(G, prof, z, r, 0, 0)
                tested += 2
                if g1 != int(stl) or g2 != int(bal):
                    mism += 1; print('MISMATCH', nx.to_graph6_bytes(G, header=False), r, g1, stl, g2, bal)
        print(f'n={n} done, queries {tested}, mismatches {mism}', flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 7)

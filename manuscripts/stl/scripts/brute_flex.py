"""Brute-force check of the T (short/long prescription) and M (pairing) constraints of tools/stl.c,
on all one-even graphs of order <= 7: for every half-set S of N(z) and every perfect matching M of
N(z), compare 'some star-terminal Lovasz D has short set exactly S' and '... has transition
pairing exactly M' with the oracle."""
import itertools
import networkx as nx
from common import Oracle, even_vertices, relabel
from brute import all_decomps

orc = Oracle()


def pairings(L):
    if not L:
        yield []
        return
    a = L[0]
    for i in range(1, len(L)):
        for rest in pairings(L[1:i] + L[i + 1:]):
            yield [(a, L[i])] + rest


def info(D, z):
    """(star?, short set, pairing) of D"""
    S = set(); M = set(); star = True
    for P in D:
        if z not in P:
            continue
        k = P.index(z); L = len(P) - 1
        sa, sb = k == 1, L - k == 1
        if not sa and not sb:
            star = False
        if sa: S.add(P[0])
        if sb: S.add(P[-1])
        M.add(frozenset((P[k - 1], P[k + 1])))
    return star, frozenset(S), frozenset(M)


def main():
    tested = mism = 0
    for n in (5, 7):
        for l in open(f'../../../data/conn{n}.g6', 'rb'):
            G = relabel(nx.from_graph6_bytes(l.strip()))
            ev = even_vertices(G)
            if len(ev) != 1:
                continue
            z = ev[0]; N = sorted(G[z]); k = len(N) // 2
            prof = {v: G.degree(v) % 2 for v in G}
            infos = [info(D, z) for D in all_decomps(G, prof)]
            for S in itertools.combinations(N, k):
                S = frozenset(S)
                truth = any(st and SS == S for st, SS, M in infos)
                # exactly S short, rest long  (an SS path makes both short, so |short| > k is excluded)
                req = {x: z for x in S}; forb = {y: z for y in N if y not in S}
                got = orc.query(G, prof, z, -1, 1, 99, req=req, forb=forb)
                tested += 1
                if got != int(truth):
                    mism += 1; print('MISMATCH S', l, S, got, truth)
            for M in pairings(N):
                Mset = frozenset(frozenset(p) for p in M)
                truth = any(st and MM == Mset for st, SS, MM in infos)
                pairs = {}
                for a, b in M:
                    pairs[a] = {b}; pairs[b] = {a}
                got = orc.query(G, prof, z, -1, 1, 99, pairs=pairs)
                tested += 1
                if got != int(truth):
                    mism += 1; print('MISMATCH M', l, M, got, truth)
    print('flex brute check: queries', tested, 'mismatches', mism)


if __name__ == '__main__':
    main()

"""A41: the real-instance failures of shape 'star + 2-chain + pair' with (H1) holding (n <= 9).

Reads the auditor's universality output (U3 lines), picks the excess-1 FAIL structures whose forest
consists of a cherry rooted at its middle (a star), a 2-path rooted at an end (a 2-chain) and an
edge (a pair), rebuilds H = (J - z) - Phi, checks (H1) at the star centre, and decides the
constraints by enumerating ALL Lovasz decompositions of H (examples_bruteforce.lovasz_decomps),
independently of the C solver.  Also reports whether H is connected.
usage: python3 -I star_chain_pair.py univ_output.txt"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from examples_bruteforce import lovasz_decomps, satisfies, hall_H1   # noqa: E402


def g6adj(s):
    n = ord(s[0]) - 63
    A = [set() for _ in range(n)]
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits += [(v >> (5 - i)) & 1 for i in range(6)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                A[i].add(j)
                A[j].add(i)
            k += 1
    return n, A


def comps(vs, adj):
    vs = set(vs)
    out = []
    while vs:
        v = vs.pop()
        c = {v}
        fr = [v]
        while fr:
            x = fr.pop()
            for y in adj[x]:
                if y in vs:
                    vs.discard(y)
                    c.add(y)
                    fr.append(y)
        out.append(c)
    return out


def main():
    seen = 0
    for line in open(sys.argv[1]):
        f = line.split()
        if not f or f[0] != "U3" or f[1] != "FAIL" or f[6] != "1":
            continue
        g, z, r = f[2], int(f[3]), int(f[4])
        par = list(map(int, f[f.index("par") + 1:]))
        n, A = g6adj(g)
        F = [set() for _ in range(n)]
        for v, p in enumerate(par):
            if p >= 0:
                F[v].add(p)
                F[p].add(v)
        cs = comps([v for v in range(n) if F[v]], F)
        if sorted(len(c) for c in cs) != [2, 3, 3] or any(max(len(F[v]) for v in c) >= 3 for c in cs):
            continue
        # relabel H on V(J) - z
        verts = [v for v in range(n) if v != z]
        idx = {v: i for i, v in enumerate(verts)}
        E = sorted({(min(idx[a], idx[b]), max(idx[a], idx[b])) for a in verts for b in A[a]
                    if b != z and par[a] != b and par[b] != a})
        avoid = {idx[v]: {idx[p]} for v, p in enumerate(par) if p >= 0}
        ch = {}
        for v, p in enumerate(par):
            if p >= 0:
                ch.setdefault(p, []).append(v)
        sibs = [(idx[X[0]], idx[X[1]]) for X in ch.values() if len(X) == 2]
        centre = [p for p, X in ch.items() if len(X) == 2][0]
        Hadj = {i: set() for i in range(len(verts))}
        for a, b in E:
            Hadj[a].add(b)
            Hadj[b].add(a)
        connected = len(comps(range(len(verts)), Hadj)) == 1
        if not all(ok for *_, ok in hall_H1(len(verts), E, idx[centre], [idx[x] for x in ch[centre]])):
            continue      # only the structures with (H1) holding at the star centre
        allD = list(lovasz_decomps(len(verts), E))
        good = [D for D in allD if satisfies(D, avoid, sibs)]
        h1 = hall_H1(len(verts), E, idx[centre], [idx[x] for x in ch[centre]])
        units = []
        for c in cs:
            rt = [v for v in c if par[v] < 0][0]
            units.append(("star" if len(ch.get(rt, [])) == 2 else ("2-chain" if len(c) == 3 else "pair"),
                          sorted(c), "root", rt))
        print(g, "z", z, "r", r, "| units", units, "| H connected:", connected,
              "| Lovasz decompositions:", len(allD), "satisfying:", len(good),
              "| (H1) at centre:", all(ok for *_, ok in h1))
        seen += 1
    print("structures:", seen)


main()

"""A41: (H1) analysis of the tier-3 universality structures (output 'U3 SUCC|FAIL g6 z r exc E par ...'
of a41 univ), to compare with data/star_hall_t1_le9.txt and to test the claim of nodata Section 5.3
that the 18 excess-1 failures with (H1) holding "come from a claw interacting with 2-chains".
(H1) is evaluated in H = B - Phi (the graph the Lovasz decomposition lives in), as in Lemma 5.4.
Own implementation (plain BFS), no networkx."""
import sys
from collections import Counter, defaultdict


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


st = Counter()
odd18 = []
for line in sys.stdin:
    f = line.split()
    if not f or f[0] != "U3":
        continue
    tag, g, z, r, exc = f[1], f[2], int(f[3]), int(f[4]), int(f[6])
    par = list(map(int, f[f.index("par") + 1:]))
    n, A = g6adj(g)
    H = [set(A[v]) - {z} if v != z else set() for v in range(n)]
    for v, p in enumerate(par):
        if p >= 0:
            H[v].discard(p)
            H[p].discard(v)
    ch = defaultdict(list)
    for v, p in enumerate(par):
        if p >= 0:
            ch[p].append(v)
    bad = False
    for u, X in ch.items():
        if len(X) < 2:
            continue
        rest = [v for v in range(n) if v != u and v != z]
        for C in comps(rest, H):
            k = len(set(X) & C)
            e = len(H[u] & C)
            if 2 * k > len(C) - e:
                bad = True
    st[(exc, tag, "H1 violated" if bad else "H1 ok")] += 1
    if tag == "FAIL" and not bad and exc == 1:
        # shape of the forest: components of Phi with their sizes; is there a claw (non-root with 2 children)?
        F = [set() for _ in range(n)]
        for v, p in enumerate(par):
            if p >= 0:
                F[v].add(p)
                F[p].add(v)
        cs = comps([v for v in range(n) if F[v]], F)
        shapes = []
        for c in cs:
            deg = sorted((len(F[v]) for v in c), reverse=True)
            shapes.append("claw%d" % (len(c) - 1) if deg[0] >= 3 else "path%d" % (len(c) - 1))
        odd18.append((g, z, r, tuple(sorted(shapes))))
for k, v in sorted(st.items()):
    print(v, k)
print("excess-1 failures with (H1) holding:", len(odd18))
print("their forest shapes:", Counter(s for *_, s in odd18))
for x in odd18:
    print("  ", *x)

#!/usr/bin/env python3
"""Audit A43: irreducible PC instances, re-derived from the manuscript text (conj31 Section 5).

Independent of scripts/stuck.c.  Reads 2-connected graphs (graph6) on stdin; for every pair
of even vertices Z and every profile b (b = 0 on Z, b == d mod 2, 1 <= b <= d elsewhere) with
(DB), tests the moves CYC, EAR, SUP, TR, NEW, TRI, SPL, TW2 and (option 'down') DOWN, exactly
as stated in Lemmas 5.1-5.9, and counts the instances to which none applies.
usage: a43_irred.py [down] [z=0|1|2] < graphs.g6
"""
import sys
from itertools import combinations


def g6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits.extend((v >> k) & 1 for k in range(5, -1, -1))
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j); adj[j].add(i)
            k += 1
    return n, adj


def connected(verts, adj):
    verts = set(verts)
    if not verts:
        return True
    s = next(iter(verts)); seen = {s}; st = [s]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y in verts and y not in seen:
                seen.add(y); st.append(y)
    return seen == verts


def twoconn(verts, adj):
    verts = set(verts)
    if len(verts) < 3 or not connected(verts, adj):
        return False
    return all(connected(verts - {x}, adj) for x in verts)


def threads(n, adj):
    """all threads x0..xm: interior of degree 2, ends of degree >= 3 (each once)"""
    deg = [len(a) for a in adj]
    out, seen = [], set()
    for x in range(n):
        if deg[x] < 3:
            continue
        for y in adj[x]:
            if (x, y) in seen:
                continue
            P = [x, y]
            while deg[P[-1]] == 2:
                nxt = [w for w in adj[P[-1]] if w != P[-2]][0]
                P.append(nxt)
            seen.add((P[0], P[1])); seen.add((P[-1], P[-2]))
            out.append(P)
    return out


def removable(P, n, adj):
    if len(P) == 2:
        a2 = [set(s) for s in adj]
        a2[P[0]].discard(P[1]); a2[P[1]].discard(P[0])
        return twoconn(range(n), a2)
    inter = set(P[1:-1])
    return twoconn(set(range(n)) - inter, adj)


def db_ok(verts, adj, b):
    S = sum(b[x] for x in verts)
    return all(len(adj[x] & verts) + b[x] <= S for x in verts)


def check_moves(n, adj, b, Z, ths, rem, down):
    deg = [len(a) for a in adj]
    V = set(range(n))
    S = sum(b)
    sl = [S - b[x] - deg[x] for x in range(n)]
    if all(d == 2 for d in deg):
        return 'CYC'
    if down:
        for x in range(n):
            if b[x] >= 3:
                b2 = list(b); b2[x] -= 2
                if db_ok(V, adj, b2):
                    return 'DOWN'
    for P, r_ok in zip(ths, rem):
        if len(P) > 2:
            inter = P[1:-1]
            r = sum(1 for z in inter if b[z] == 2)
            if r_ok and r >= 1 and not (r == 1 and P[0] in Z and P[-1] in Z):
                return 'EAR'
            if all(z in Z for z in inter) and len(inter) <= 2 and P[-1] not in adj[P[0]]:
                return 'SUP'
    for P, r_ok in zip(ths, rem):
        if len(P) != 2 or not r_ok:
            continue
        p, q = P
        for x, y in ((p, q), (q, p)):
            # TR: b' = b + 1_x - 1_y on B - xy
            if b[y] >= 1 and b[x] <= deg[x] - 2:
                Z2 = (set(Z) - {x}) | ({y} if b[y] == 1 else set())
                Ny = adj[y] - {x}
                if len(Z2) <= 2 and len(Ny & Z2) <= b[x]:
                    return 'TR'
        if b[p] >= 1 and b[q] >= 1:
            Z2 = set(Z) | ({p} if b[p] == 1 else set()) | ({q} if b[q] == 1 else set())
            if len(Z2) <= 2 and all(sl[w] >= 2 for w in range(n) if w not in (p, q)):
                return 'NEW'
    for u in Z:
        if deg[u] != 2:
            continue
        x, y = sorted(adj[u])
        if y not in adj[x] or x in Z or y in Z:
            continue
        if not twoconn(V - {u}, adj):
            continue
        other = [z for z in Z if z != u]
        for xx, yy in ((x, y), (y, x)):
            if b[xx] <= deg[xx] - 2 and (not other or other[0] not in adj[yy] or b[xx] >= 2):
                return 'TRI'
    for x in range(n):
        if x in Z or b[x] != deg[x] or len(adj[x] & set(Z)) > 1:
            continue
        if not twoconn(V - {x}, adj):
            continue
        b2 = list(b); b2[x] = 0
        for y in adj[x]:
            b2[y] = b[y] + 1 if b[y] <= deg[y] - 2 else b[y] - 1
        a2 = [s - {x} for s in adj]; a2[x] = set()
        W = V - {x}
        if sum(1 for w in W if b2[w] == 0) <= 2 and db_ok(W, a2, b2):
            return 'SPL'
    if len(Z) == 2:
        u, v = Z
        if v not in adj[u] and adj[u] == adj[v] and len(adj[u]) == 2:
            x, y = sorted(adj[u])
            if y not in adj[x]:
                a2 = [s - {u, v} for s in adj]; a2[u] = set(); a2[v] = set()
                a2[x].add(y); a2[y].add(x)
                W = V - {u, v}
                b2 = list(b); b2[x] -= 1; b2[y] -= 1
                if twoconn(W, a2) and sum(1 for w in W if b2[w] == 0) <= 2 and db_ok(W, a2, b2):
                    return 'TW2'
    return None


def main():
    down = 'down' in sys.argv
    zs = 2
    for a in sys.argv[1:]:
        if a.startswith('z='):
            zs = int(a[2:])
    inst = stuck = twin = minimal = 0
    cnt = {}
    for line in sys.stdin:
        s = line.strip()
        if not s:
            continue
        n, adj = g6(s)
        deg = [len(a) for a in adj]
        ev = [x for x in range(n) if deg[x] > 0 and deg[x] % 2 == 0]
        ths = threads(n, adj) if not all(d == 2 for d in deg) else []
        rem = [removable(P, n, adj) for P in ths]
        for Z in combinations(ev, zs):
            choices = []
            for x in range(n):
                if x in Z:
                    choices.append([0])
                else:
                    choices.append(list(range(1 if deg[x] % 2 else 2, deg[x] + 1, 2)))
            stack = [[]]
            profiles = [[]]
            for c in choices:
                profiles = [p + [v] for p in profiles for v in c]
            for b in profiles:
                if not db_ok(set(range(n)), adj, b):
                    continue
                inst += 1
                m = check_moves(n, adj, b, Z, ths, rem, down)
                cnt[m] = cnt.get(m, 0) + 1
                if m is None:
                    stuck += 1
                    tw = len(Z) == 2 and (adj[Z[0]] - {Z[1]}) == (adj[Z[1]] - {Z[0]})
                    twin += tw
                    mz = all(b[x] == (1 if deg[x] % 2 else 2) for x in range(n) if x not in Z)
                    minimal += mz
                    print('STUCK%s %s b=%s%s' % ('_TWIN' if tw else '', s, ','.join(map(str, b)), ' minimal' if mz else ''))
    print('zeros %d down %s: instances %d irreducible %d twin %d minimal-profile %d  moves %s' % (
        zs, down, inst, stuck, twin, minimal, {k: v for k, v in cnt.items() if k}))


if __name__ == '__main__':
    main()

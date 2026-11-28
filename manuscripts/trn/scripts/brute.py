#!/usr/bin/env python3
"""brute.py: independent brute-force check of chain.cpp.
Enumerates Lovász decompositions by a different method (repeatedly take the first unused edge and
enumerate every path through it), simulates Fan's forced chain independently, and prints, for each
TRN instance (G,g,y,x,u) with (G-gu,y,{x}) good, the triple (nD, nAvoid, nGood).
Usage: python3 brute.py < graphs.g6  (small orders only)."""
import sys

def parse_g6(s):
    s = s.strip(); n = ord(s[0]) - 63; bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for k in range(5, -1, -1): bits.append((v >> k) & 1)
    adj = [set() for _ in range(n)]; p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]: adj[i].add(j); adj[j].add(i)
            p += 1
    return n, adj

def decomps(n, adj):
    """all decompositions into paths with b(v) = deg(v) mod 2; paths as vertex tuples."""
    edges = sorted({(min(a, b), max(a, b)) for a in range(n) for b in adj[a]})
    eid = {e: i for i, e in enumerate(edges)}
    need = [len(adj[v]) % 2 for v in range(n)]
    used = [False] * len(edges); ends = [0] * n; out = []; cur = []
    def eidx(a, b): return eid[(min(a, b), max(a, b))]
    def paths_through(i):
        a, b = edges[i]
        # extend a simple path [.., a, b, ..] in both directions
        res = []
        def ext_right(path, vis):
            yield path
            t = path[-1]
            for w in adj[t]:
                if w in vis or used[eidx(t, w)]: continue
                yield from ext_right(path + [w], vis | {w})
        def ext_left(path, vis):
            for p in ext_right(path, vis):
                yield p
            h = path[0]
            for w in adj[h]:
                if w in vis or used[eidx(h, w)]: continue
                yield from ext_left([w] + path, vis | {w})
        # to avoid duplicates generate: left extensions first fixed, then right extensions
        seen = set()
        for p in ext_left([a, b], {a, b}):
            key = tuple(p) if p[0] < p[-1] else tuple(reversed(p))
            if key not in seen: seen.add(key); res.append(p)
        return res
    def rec():
        try: i = used.index(False)
        except ValueError:
            if ends == need: out.append([tuple(p) for p in cur])
            return
        for p in paths_through(i):
            s, t = p[0], p[-1]
            if ends[s] + 1 > need[s] or ends[t] + 1 > need[t]: continue
            ids = [eidx(p[k], p[k + 1]) for k in range(len(p) - 1)]
            for j in ids: used[j] = True
            ends[s] += 1; ends[t] += 1; cur.append(p)
            rec()
            cur.pop(); ends[s] -= 1; ends[t] -= 1
            for j in ids: used[j] = False
    rec()
    return out

def fan(D, t, w):
    """Fan's forced chain: add edge t-w. Returns (new decomposition, chain list)."""
    P = [list(p) for p in D]; chain = []; x = t
    # the path of the ORIGINAL decomposition ending at x (it may since have been re-routed at its
    # other end, which keeps this end)
    orig = {}
    for i, p in enumerate(D):
        for v in (p[0], p[-1]):
            assert v not in orig; orig[v] = i
    while True:
        chain.append(x)
        idx = [orig[x]]
        p = P[idx[0]]
        assert p[0] == x or p[-1] == x
        if p[-1] == x: p.reverse()
        if w not in p:
            P[idx[0]] = [w] + p; return P, chain
        k = p.index(w); y = p[k - 1]
        P[idx[0]] = list(reversed(p[:k])) + p[k:]
        x = y

def main():
    for line in sys.stdin:
        line = line.strip()
        if not line: continue
        n, adj = parse_g6(line)
        ev = [v for v in range(n) if adj[v] and len(adj[v]) % 2 == 0]
        if len(ev) != 1: continue
        g = ev[0]
        for u in sorted(adj[g]):
            H = [set(a) for a in adj]; H[g].discard(u); H[u].discard(g)
            DS = decomps(n, H)
            for y in range(n):
                if len(adj[y]) % 2 == 0 or u not in adj[y]: continue
                for x in range(n):
                    if x == y or x == u or len(adj[x]) % 2 == 0 or x in adj[y]: continue
                    nD = nAv = nGood = 0
                    for D in DS:
                        Q = [p for p in D if p[0] == y or p[-1] == y]
                        assert len(Q) == 1
                        if x in Q[0]: continue
                        nD += 1
                        R, ch = fan(D, g, u)
                        if y not in ch: nAv += 1
                        Q2 = [p for p in R if p[0] == y or p[-1] == y]
                        if x not in Q2[0]: nGood += 1
                    if nD: print(line, g, y, x, u, nD, nAv, nGood)

if __name__ == "__main__":
    main()

"""v_enum.py: independent pure-Python enumerator of path decompositions with prescribed end counts,
by PATH GROWING (a different algorithm from the transition systems of a25.h).  Reads the lines
"g6 bvector count hash" written by v_enum.cpp, recomputes count and hash, and reports mismatches.

Algorithm: repeatedly take the smallest vertex v that still needs an end (b'(v) > 0) and has an
unused edge; grow a path from v edge by edge (no repeated vertex); the path may be closed at any
vertex w != v with b'(w) > 0.  When no vertex needs an end, all edges must be used.  Each
decomposition is produced once per choice of start; canonical keys remove the orientation."""
import sys

def g6decode(s):
    s = s.strip(); n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        x = ord(ch) - 63
        bits += [(x >> k) & 1 for k in range(5, -1, -1)]
    E = set(); p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]: E.add((i, j))
            p += 1
    return n, E

def hstr(s):
    h = 1469598103934665603
    for ch in s.encode():
        h ^= ch; h = (h * 1099511628211) % (1 << 64)
    return h

def decomps(n, E, b):
    adj = {v: set() for v in range(n)}
    for (u, v) in E: adj[u].add(v); adj[v].add(u)
    used = set(); need = list(b); out = []
    def key(D):
        ps = []
        for P in D:
            P = list(P)
            if P[0] > P[-1]: P.reverse()
            ps.append(''.join(chr(97 + x) for x in P))
        ps.sort(); return ''.join(s + '|' for s in ps)
    D = []
    def rest():
        if len(used) == len(E):
            if all(x == 0 for x in need): out.append(key(D))
            return
        starts = [v for v in range(n) if need[v] > 0]
        if not starts: return
        v = starts[0]
        # v must start a path now (every path has both ends among vertices needing ends; take the smallest)
        if not any(frozenset((v, w)) not in used for w in adj[v]): return
        P = [v]; D.append(P)
        grow(v, P)
        D.pop()
    def grow(v, P):
        x = P[-1]
        for w in sorted(adj[x]):
            e = frozenset((x, w))
            if e in used or w in P: continue
            used.add(e); P.append(w)
            if need[w] > 0 and w != v:
                need[v] -= 1; need[w] -= 1
                rest()
                need[v] += 1; need[w] += 1
            grow(v, P)
            P.pop(); used.discard(e)
    rest()
    return out

mism = 0; tot = 0
for line in sys.stdin:
    g6, bstr, cnt, h = line.split()
    n, E = g6decode(g6)
    b = [int(ch) for ch in bstr]
    keys = decomps(n, E, b)
    # with b(v) >= 2 the same decomposition can be grown in several orders; compare sets
    ks = set(keys)
    H = sum(hstr(k) for k in ks) % (1 << 64)
    tot += 1
    if len(ks) != int(cnt) or H != int(h):
        mism += 1
        print("MISMATCH", g6, bstr, "c++", cnt, "py", len(ks), len(keys))
print("checked", tot, "mismatches", mism)

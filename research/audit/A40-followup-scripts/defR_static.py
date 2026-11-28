"""defR_static.py -- static check of the shipped Criterion R certificates against ln.tex Def. 6.2
(commit 61abb4e): for every 'OK kind g6 c1 a1 c2 a2 P=... moves=k' line, identify i from P[0],
and check P is a path of F starting at c_i, avoiding a_i; in 'joint' lines P ends at c_j and avoids
a_j (Def 6.2(a)); in 'pre' lines P ends outside {c_j, a_j} (Def 6.2(b)).  Also records which tail
form routeR would use (leaf variant iff c_j has degree 1 in K_0 with stem w and a_j not in {w} u N(w)),
and whether P passes through c_j or a_j.  (Audit A40 Sec. 3(c) already re-verified and re-executed
every certificate; this only confirms the match with the new wording.)
usage: python3 defR_static.py FILE"""
import sys

def g6_decode(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits += [(v >> k) & 1 for k in range(5, -1, -1)]
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]: adj[i].add(j); adj[j].add(i)
            k += 1
    return n, adj

stats = {}
bad = 0
for line in open(sys.argv[1]):
    t = line.split()
    kind, g = t[1], t[2]
    c1, a1, c2, a2 = map(int, t[3:7])
    P = list(map(int, t[7][2:].split('-')))
    n, adj = g6_decode(g)
    if P[0] == c1: ci, ai, cj, aj = c1, a1, c2, a2
    elif P[0] == c2: ci, ai, cj, aj = c2, a2, c1, a1
    else: print('P does not start at c1 or c2', line); bad += 1; continue
    ok = len(P) >= 2 and len(set(P)) == len(P) and all(b in adj[a] for a, b in zip(P, P[1:])) and ai not in P
    p = P[-1]
    if kind == 'joint':
        ok = ok and p == cj and aj not in P
        form = 'a'
    else:
        ok = ok and p not in (cj, aj) and cj not in P
        E = set(frozenset((u, v)) for u in range(n) for v in adj[u]) - set(frozenset(e) for e in zip(P, P[1:]))
        A0 = [set() for _ in range(n)]
        for e in E:
            u, v = tuple(e); A0[u].add(v); A0[v].add(u)
        if len(A0[cj]) == 1:
            w = next(iter(A0[cj]))
            form = 'b-leafvariant' if (aj != w and aj not in A0[w]) else 'b-ell(c_j leaf, a_j near stem)'
        else:
            form = 'b-ell'
        if aj in P: form += ', a_j interior of P'
    if not ok: bad += 1; print('BAD', line.strip())
    stats[form] = stats.get(form, 0) + 1
print(sys.argv[1], 'lines', sum(stats.values()), 'bad', bad, stats)

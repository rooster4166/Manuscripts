"""precommit.py -- route 3 (provable): fix Q(c_i) = P (a path from c_i avoiding a_i, of length <= L),
delete E(P), hang a leaf at the other tail c_j (or use it as a leaf tail if it is a leaf of F at
distance >= 3 from a_j) and look for a token schedule (moves M, D, S; fin: <= 1 token and the
live heads sparse, Theorem A).  If P ends at c_j and avoids a_j too, the tail of c_j is dropped
(joint route).  Reads 'g6 c1 a1 c2 a2'; prints residual instances."""
import sys
from lnlib import g6_decode
from sched3 import run as _unused
def schedule(N, E, tails):
    seen = {}
    def degs(E):
        d = [0] * N
        for u, v in E: d[u] += 1; d[v] += 1
        return d
    def search(E, tails):
        key = (E, tails)
        if key in seen: return seen[key]
        seen[key] = False
        d = [0] * N; A = [set() for _ in range(N)]
        for u, v in E: d[u] += 1; d[v] += 1; A[u].add(v); A[v].add(u)
        tok = [v for v in range(N) if d[v] > 0 and d[v] % 2 == 0]
        if len(tok) <= 1:
            xs = set(x for (_, _, x) in tails)
            if all(len(A[v] & xs) <= 1 for v in range(N)): seen[key] = True; return True
        ts = set(tok); X = set()
        for (c, s, x) in tails: X |= {c, x}
        for p in tok:
            for u in A[p]:
                if d[u] % 2 == 0 or u in X: continue
                if any(w in ts and w != p for w in A[u] if w != p): continue
                if search(E - {(min(p, u), max(p, u))}, tails): seen[key] = True; return True
        for i, (c, s, x) in enumerate(tails):
            if d[s] % 2 == 1:
                if search(E - {(min(c, s), max(c, s))}, tails[:i] + tails[i+1:]): seen[key] = True; return True
        leaves = {c for (c, s, x) in tails}
        for p in tok:
            if d[p] != 2: continue
            a, b = sorted(A[p])
            if b in A[a] or a in leaves or b in leaves: continue
            if any({a, b} == {x, s} for (c, s, x) in tails): continue
            E2 = (E - {(min(p, a), max(p, a)), (min(p, b), max(p, b))}) | {(a, b)}
            if search(frozenset(E2), tails): seen[key] = True; return True
        return False
    return search(frozenset(E), tuple(tails))
def route3(n, adj, ci, ai, cj, aj, L=4):
    E0 = set((u, v) for u in range(n) for v in adj[u] if u < v)
    paths = []
    def ext(P, S):
        if len(P) >= 2: paths.append(list(P))
        if len(P) > L or P[-1] == cj and len(P) >= 2: return
        for y in adj[P[-1]]:
            if y not in S and y != ai:
                S.add(y); P.append(y); ext(P, S); P.pop(); S.discard(y)
    ext([ci], {ci})
    for P in paths:
        E = E0 - set((min(p, q), max(p, q)) for p, q in zip(P, P[1:]))
        if P[-1] == cj:
            if aj in P: continue
            tails = []; N = n
        else:
            N = n
            A = [set() for _ in range(n)]
            for u, v in E: A[u].add(v); A[v].add(u)
            if len(A[cj]) == 1 and aj not in A[next(iter(A[cj]))] and aj != next(iter(A[cj])):
                tails = [(cj, next(iter(A[cj])), aj)]
            elif len(A[cj]) == 0:
                continue  # c_j isolated: its end path would be P itself, handled by the joint case
            else:
                E = E | {(cj, n)}; tails = [(n, cj, aj)]; N = n + 1
        if schedule(N, E, tails): return True
    return False
if __name__ == '__main__':
    tot = left = 0
    for line in sys.stdin:
        t = line.split()
        if not t: continue
        n, adj = g6_decode(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
        tot += 1
        if not (route3(n, adj, c1, a1, c2, a2) or route3(n, adj, c2, a2, c1, a1)):
            left += 1; print(line.strip(), flush=True)
    print('input', tot, 'left after route 3', left, file=sys.stderr)

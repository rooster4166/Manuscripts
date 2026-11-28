"""joint_sched.py -- the joint route with a provable finish: a path P from c1 to c2 avoiding a1, a2
such that F - E(P) has a token schedule with no tails (moves M, S; fin: at most one token).
Then F - E(P) has a parity decomposition (multi-token steerK_good with T empty), and adding P gives
a Lovasz decomposition with Q(c1) = Q(c2) = P.  Reads 'g6 c1 a1 c2 a2'; prints per-instance flag."""
import sys
from lnlib import g6_decode
def free_sched(N, E):
    seen = {}
    def degs(E):
        d = [0] * N
        for u, v in E: d[u] += 1; d[v] += 1
        return d
    def search(E):
        if E in seen: return seen[E]
        seen[E] = False
        d = [0] * N; A = [set() for _ in range(N)]
        for u, v in E: d[u] += 1; d[v] += 1; A[u].add(v); A[v].add(u)
        tok = [v for v in range(N) if d[v] > 0 and d[v] % 2 == 0]
        if len(tok) <= 1: seen[E] = True; return True
        ts = set(tok)
        for p in tok:
            for u in A[p]:
                if d[u] % 2 == 0: continue
                if any(w in ts and w != p for w in A[u] if w != p): continue
                if search(E - {(min(p, u), max(p, u))}): seen[E] = True; return True
        for p in tok:
            if d[p] != 2: continue
            a, b = sorted(A[p])
            if b in A[a]: continue
            E2 = (E - {(min(p, a), max(p, a)), (min(p, b), max(p, b))}) | {(a, b)}
            if search(frozenset(E2)): seen[E] = True; return True
        return False
    return search(frozenset(E))
def joint_ok(n, adj, c1, a1, c2, a2, maxlen=None):
    E = set((u, v) for u in range(n) for v in adj[u] if u < v)
    found = [False]
    def ext(P, S):
        if found[0]: return
        x = P[-1]
        if x == c2:
            Ep = set((min(p, q), max(p, q)) for p, q in zip(P, P[1:]))
            if free_sched(n, E - Ep): found[0] = True
            return
        if maxlen and len(P) > maxlen: return
        for y in adj[x]:
            if y not in S and y not in (a1, a2):
                S.add(y); P.append(y); ext(P, S); P.pop(); S.discard(y)
    ext([c1], {c1})
    return found[0]
if __name__ == '__main__':
    tot = ok = 0
    for line in sys.stdin:
        t = line.split()
        if not t: continue
        n, adj = g6_decode(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
        r = joint_ok(n, adj, c1, a1, c2, a2)
        tot += 1; ok += r
        print(('J1 ' if r else 'J0 ') + line.strip(), flush=True)
    print('total', tot, 'joint+free schedule', ok, file=sys.stderr)

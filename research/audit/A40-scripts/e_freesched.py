"""e_freesched.py -- reproduce the 'Lemma R(a) with a free schedule' row (order 8) with own code:
some path P from c1 to c2 avoiding a1, a2 such that F - E(P) has a token schedule with no tails
(moves M and S of multi-token Def. 2.2; end: at most one token).  Also counts the union with the
joint-decomposition row is NOT computed here.  usage: python3 e_freesched.py INST [start step]"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a40lib import dec

def ek(a, b): return (a, b) if a < b else (b, a)

def has_sched(n, E):
    failed = set()
    def rec(E):
        if E in failed: return False
        A = [set() for _ in range(n)]
        for u, v in E: A[u].add(v); A[v].add(u)
        tok = [v for v in range(n) if A[v] and len(A[v]) % 2 == 0]
        if len(tok) <= 1: return True
        ts = set(tok)
        for p in tok:
            for u in A[p]:
                if len(A[u]) % 2 == 1 and not ((A[u] - {p}) & ts):
                    if rec(E - {ek(p, u)}): return True
        for p in tok:
            if len(A[p]) == 2:
                a, b = A[p]
                if b not in A[a]:
                    if rec((E - {ek(p, a), ek(p, b)}) | {ek(a, b)}): return True
        failed.add(E)
        return False
    return rec(frozenset(E))

def ok(n, F, c1, a1, c2, a2):
    EF = frozenset(ek(u, v) for u in range(n) for v in F[u])
    st = []
    def ext(P, S):
        x = P[-1]
        if x == c2:
            return has_sched(n, EF - {ek(p, q) for p, q in zip(P, P[1:])})
        for y in F[x]:
            if y not in S and y not in (a1, a2):
                S.add(y); P.append(y)
                if ext(P, S): return True
                P.pop(); S.discard(y)
        return False
    return ext([c1], {c1})

lines = [l.split() for l in open(sys.argv[1]) if l.strip()]
s0, step = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
cnt = tot = 0
for t in lines[s0::step]:
    n, F = dec(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
    tot += 1; cnt += ok(n, F, c1, a1, c2, a2)
print('instances', tot, 'R(a) with free schedule', cnt, flush=True)

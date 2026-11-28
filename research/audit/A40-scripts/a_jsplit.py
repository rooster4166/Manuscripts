"""a_jsplit.py -- decide instances with one J constraint without J: enumerate every p-q path P that
respects the constraints on the joined path, and solve F - E(P) (with r(p) = r(q) reduced by one) by
trsolve with its failure memo.  Used for the cross-check lines that trsolve left undecided."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a40lib import dec, enc, solve_lines
for line in sys.stdin:
    t = line.split()
    if not t: continue
    n, A = dec(t[0]); req = [len(a) % 2 for a in A]
    cons = [(t[i], int(t[i + 1]), int(t[i + 2])) for i in range(1, len(t), 3)]
    for c in cons:
        if c[0] == 'R': req[c[1]] = c[2]
    (p, q), = [(c[1], c[2]) for c in cons if c[0] == 'J']
    av = [(c[1], c[2]) for c in cons if c[0] == 'A']
    sp = [(c[1], c[2]) for c in cons if c[0] == 'S']
    paths = []
    def ext(P, S):
        if P[-1] == q:
            paths.append(list(P)); return
        for y in A[P[-1]]:
            if y not in S:
                S.add(y); P.append(y); ext(P, S); P.pop(); S.discard(y)
    ext([p], {p})
    queries = []
    for P in paths:
        V = set(P)
        if any(x in (p, q) and a in V for x, a in av): continue
        if any(a in V and b in V for a, b in sp): continue
        B = [set(a) for a in A]
        for x, y in zip(P, P[1:]): B[x].discard(y); B[y].discard(x)
        r2 = list(req); r2[p] -= 1; r2[q] -= 1
        rs = ''.join(' R %d %d' % (v, r2[v]) for v in range(n) if r2[v] != len(B[v]) % 2 or v in (p, q))
        qa = ''.join(' A %d %d' % (x, a) for x, a in av if x not in (p, q))
        qs = ''.join(' S %d %d' % s for s in sp)
        queries.append(enc(n, B) + rs + qa + qs)
    res = solve_lines(queries, budget=2000000000) if queries else []
    ans = [r[0] for r in res]
    verdict = 'SAT' if 'SAT' in ans else ('UNDEC' if 'UNDEC' in ans else 'UNSAT')
    print(verdict, line.strip(), 'paths tried', len(queries), flush=True)

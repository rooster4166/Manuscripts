"""pall.py -- for every L_N(2) instance, every orientation i and every path P from c_i avoiding a_i
(c_j allowed only as the last vertex, as in routeR; option -int also allows c_j interior), decide
Lemma R's hypothesis exactly with lnsolve:
  (a) P ends at c_j, a_j not on P: K0 = F - E(P) has a parity decomposition;
  (b) otherwise: K0 + c_j l has a parity decomposition with l, a_j on no common path.
Output per instance: 'inst | o:P:kind:res ...' with kind a, b (end not a_j), z (end a_j).
usage: pall.py LNSOLVE [-int] < instances"""
import sys, subprocess
from multiprocessing import Pool
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode, g6_encode

SOLVER = None; INTERIOR = False

def ekey(a, b): return (a, b) if a < b else (b, a)

def g6_of(N, E):
    A = [set() for _ in range(N)]
    for u, v in E: A[u].add(v); A[v].add(u)
    return g6_encode(N, A)

def paths_from(adj, ci, ai, cj):
    out = []
    def ext(P, S):
        if len(P) >= 2: out.append(tuple(P))
        if P[-1] == cj and len(P) >= 2 and not INTERIOR: return
        for y in sorted(adj[P[-1]]):
            if y not in S and y != ai:
                S.add(y); P.append(y); ext(P, S); P.pop(); S.discard(y)
    ext([ci], {ci})
    return out

def work(lines):
    queries = []; recs = []
    for line in lines:
        t = line.split()
        n, adj = g6_decode(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
        E0 = set(ekey(u, v) for u in range(n) for v in adj[u])
        rec = []
        for o, (ci, ai, cj, aj) in enumerate(((c1, a1, c2, a2), (c2, a2, c1, a1))):
            for P in paths_from(adj, ci, ai, cj):
                E = E0 - set(ekey(p, q) for p, q in zip(P, P[1:]))
                if P[-1] == cj:
                    if aj in P: continue
                    kind = 'a'; q = g6_of(n, E)
                else:
                    kind = 'z' if P[-1] == aj else 'b'
                    q = g6_of(n + 1, E | {(cj, n)}) + ' S %d %d' % (n, aj)
                rec.append([o, P, kind, None]); queries.append(q)
        recs.append((line.strip(), rec))
    res = subprocess.run([SOLVER, '-b', '20000000'], input='\n'.join(queries) + '\n',
                         capture_output=True, text=True).stdout.split('\n')
    out = []; k = 0
    for line, rec in recs:
        for r in rec:
            r[3] = {'SAT': 'S', 'UNSAT': 'U', 'UNDEC': 'D'}.get(res[k].split()[0], '?') if res[k] else '?'; k += 1
        out.append(line + ' | ' + ' '.join('%d:%s:%s:%s' % (r[0], '-'.join(map(str, r[1])), r[2], r[3]) for r in rec))
    return out

if __name__ == '__main__':
    SOLVER = sys.argv[1]; INTERIOR = '-int' in sys.argv
    lines = [l for l in sys.stdin if l.strip()]
    chunks = [lines[i:i + 50] for i in range(0, len(lines), 50)]
    with Pool(4, initializer=lambda s, it: globals().update(SOLVER=s, INTERIOR=it), initargs=(SOLVER, INTERIOR)) as pool:
        for out in pool.imap(work, chunks):
            for o in out: print(o)
            sys.stdout.flush()

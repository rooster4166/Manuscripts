"""pscan.py -- for every L_N(2) instance and every single-edge pre-committed path P = c_i x,
record: kind (a: x = c_j; b: x not in {c_j, a_j}; z: x = a_j), whether a token schedule exists
(Criterion R, routeR.search), and whether Lemma R's hypothesis holds exactly (lnsolve).
usage: pscan.py LNSOLVE < instances > out"""
import sys, subprocess, os
from multiprocessing import Pool
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode, g6_encode
from routeR import search, ekey

SOLVER = None

def tails_for(n, E, cj, aj):
    A = [set() for _ in range(n)]
    for u, v in E: A[u].add(v); A[v].add(u)
    if len(A[cj]) == 1:
        w = next(iter(A[cj]))
        if aj != w and aj not in A[w]:
            return n, E, [(cj, w, aj)]
    return n + 1, E | {(cj, n)}, [(n, cj, aj)]

def g6_of(N, E):
    A = [set() for _ in range(N)]
    for u, v in E: A[u].add(v); A[v].add(u)
    return g6_encode(N, A)

def work(lines):
    out = []
    queries = []
    recs = []
    for line in lines:
        t = line.split()
        n, adj = g6_decode(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
        E0 = set(ekey(u, v) for u in range(n) for v in adj[u])
        rec = []
        for idx, (ci, ai, cj, aj) in enumerate(((c1, a1, c2, a2), (c2, a2, c1, a1))):
            for x in sorted(adj[ci]):
                E = E0 - {ekey(ci, x)}
                if x == cj:
                    kind = 'a'; N = n; tails = []; EK = E
                    q = g6_of(n, E)
                else:
                    kind = 'z' if x == aj else 'b'
                    N, EK, tails = tails_for(n, E, cj, aj)
                    # exact query always with a fresh leaf l = n
                    q = g6_of(n + 1, E | {(cj, n)}) + ' S %d %d' % (n, aj)
                sch = None
                if kind != 'z':
                    sch = search(N, EK, tails) is not None
                rec.append([idx, x, kind, sch, None])
                queries.append(q)
        recs.append((line.strip(), rec))
    res = subprocess.run([SOLVER, '-b', '20000000'], input='\n'.join(queries) + '\n',
                         capture_output=True, text=True).stdout.split('\n')
    k = 0
    for line, rec in recs:
        for r in rec:
            s = {'SAT': 'S', 'UNSAT': 'U', 'UNDEC': 'D'}.get(res[k].split()[0], '?') if res[k] else '?'; k += 1
            r[4] = s
        out.append(line + ' | ' + ' '.join('%d:%d:%s:%s:%s' % (r[0], r[1], r[2],
                   '-' if r[3] is None else ('Y' if r[3] else 'N'), r[4][0]) for r in rec))
    return out

if __name__ == '__main__':
    SOLVER = sys.argv[1]
    lines = [l for l in sys.stdin if l.strip()]
    chunks = [lines[i:i + 200] for i in range(0, len(lines), 200)]
    with Pool(4) as pool:
        for out in pool.imap(work, chunks):
            for o in out: print(o)
            sys.stdout.flush()

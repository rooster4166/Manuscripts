"""xcheckb.py: cross-check the far-end oracle (orcb.h, via ./qb) against full enumeration of
Lovasz decompositions (dl-one/scripts/enum).  For every graph on stdin (graph6), every odd c, every
A and every B (B odd, outside A + c), compare.  usage: xcheckb.py < graph6"""
import sys, subprocess, itertools, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../dl-one/scripts'))
from dllib import g6_decode, adjsets
ENUM = os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../dl-one/scripts/enum')
QB = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'qb')
tot = mism = 0; skipped = 0
for line in sys.stdin:
    s = line.strip()
    if not s: continue
    n, E = g6_decode(s); Adj = adjsets(n, E)
    deg = [len(Adj[v]) for v in range(n)]
    if sum(1 for d in deg if d > 0 and d % 2 == 0) > 1: continue
    out = subprocess.run([ENUM, '2000000'], input='%d %d %s\n' % (n, len(E), ' '.join('%d %d' % e for e in E)),
                         capture_output=True, text=True).stdout.splitlines()
    if out[-1] == 'END CAP': skipped += 1; continue
    odd = [v for v in range(n) if deg[v] % 2 == 1]
    pairs = {c: set() for c in odd}
    for d in out[:-1]:
        for p in d.split('|'):
            P = list(map(int, p.split()))
            for c, f in ((P[0], P[-1]), (P[-1], P[0])):
                if c in pairs: pairs[c].add((frozenset(P), f))
    queries = []
    for c in odd:
        others = [v for v in range(n) if v != c]
        for k in range(len(others) + 1):
            for A in itertools.combinations(others, k):
                Aset = set(A); Bc = [v for v in odd if v != c and v not in Aset]
                for kb in range(len(Bc) + 1):
                    for B in itertools.combinations(Bc, kb):
                        truth = any(not (V & Aset) and f not in B for (V, f) in pairs[c])
                        queries.append((c, sum(1 << a for a in A), sum(1 << b for b in B), truth))
    inp = s + '\n' + '\n'.join('%d %d %d' % q[:3] for q in queries) + '\n'
    res = subprocess.run([QB], input=inp, capture_output=True, text=True).stdout.split()
    for q, r in zip(queries, res):
        tot += 1
        if (r == '1') != q[3]: mism += 1; print('MISMATCH', s, q, r)
print('XCHECKB queries=%d mismatches=%d graphs_skipped_cap=%d' % (tot, mism, skipped))

"""an7.py -- case (a) (joint P) at order 8: exact and schedule coverage by canonical rules."""
import sys, collections
from multiprocessing import Pool
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
from routeR import search, ekey
def work(line):
    inst, rest = line.split(' | ')
    t = inst.split(); n, adj = g6_decode(t[0]); c1,a1,c2,a2 = map(int,t[1:5])
    E0 = set(ekey(u, v) for u in range(n) for v in adj[u])
    A = []
    for r in rest.split():
        o, P, kind, res = r.split(':')
        if kind == 'a' and o == '0': A.append((tuple(map(int,P.split('-'))), res))
    if not A: return None
    mn = min(len(P) for P,_ in A); mx = max(len(P) for P,_ in A)
    out = {'exact_any': any(r=='S' for _,r in A),
           'exact_some_short': any(r=='S' for P,r in A if len(P)==mn),
           'exact_all_short': all(r=='S' for P,r in A if len(P)==mn),
           'exact_some_long': any(r=='S' for P,r in A if len(P)==mx),
           'exact_all_long': all(r=='S' for P,r in A if len(P)==mx)}
    sched = {}
    for P, r in sorted(A, key=lambda x: len(x[0])):
        if r != 'S': sched[P] = False; continue
        E = frozenset(E0 - set(ekey(p, q) for p, q in zip(P, P[1:])))
        sched[P] = search(n, E, []) is not None
    out['sched_any'] = any(sched.values())
    out['sched_some_short'] = any(sched[P] for P,_ in A if len(P)==mn)
    out['sched_some_long'] = any(sched[P] for P,_ in A if len(P)==mx)
    out['nexact'] = sum(r=='S' for _,r in A); out['nsched'] = sum(sched.values()); out['n'] = len(A)
    return inst, out
if __name__ == '__main__':
    C = collections.Counter(); bad = []
    with Pool(4) as pool:
        for res in pool.imap_unordered(work, open('pall8.out'), chunksize=50):
            if res is None: continue
            inst, out = res
            C['inst'] += 1
            for k in out:
                if k in ('nexact','nsched','n'): C[k] += out[k]
                else: C[k] += out[k]
            if out['exact_any'] and not out['sched_any']: bad.append(inst)
    for k in sorted(C): print(k, C[k])
    print('exact but no case-(a) schedule:', bad)

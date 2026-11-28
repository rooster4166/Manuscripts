"""cov.py -- coverage of the proved sufficient conditions (C1)-(C3) for the joint case at order 8."""
import sys, collections
from multiprocessing import Pool
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
def ekey(a, b): return (a, b) if a < b else (b, a)

def static_steer(n, E, g, h):
    """trail from g, every vertex after g outside N[h] (current graph), ending at a vertex that
    the trail leaves isolated (the token retires).  E: frozenset of edges."""
    A = [set() for _ in range(n)]
    for u, v in E: A[u].add(v); A[v].add(u)
    X = A[h] | {h}
    seen = set()
    def rec(p, E):
        key = (p, E)
        if key in seen: return False
        seen.add(key)
        Ad = [set() for _ in range(n)]
        for u, v in E: Ad[u].add(v); Ad[v].add(u)
        for u in Ad[p]:
            if u in X: continue
            E2 = E - {ekey(p, u)}
            if len(Ad[u]) == 1: return True           # u becomes isolated: retire
            if rec(u, E2): return True
        return False
    return rec(g, E)

def work(line):
    inst, rest = line.split(' | ')
    t = inst.split(); n, adj = g6_decode(t[0]); c1,a1,c2,a2 = map(int,t[1:5])
    E0 = frozenset(ekey(u, v) for u in range(n) for v in adj[u])
    A = [tuple(map(int,r.split(':')[1].split('-'))) for r in rest.split() if r.split(':')[2]=='a' and r.split(':')[0]=='0']
    if not A: return None
    res = {'C1': len(adj[c1]) == 1 or len(adj[c2]) == 1, 'C2': False, 'C3': False}
    for P in A:
        E = E0 - set(ekey(p, q) for p, q in zip(P, P[1:]))
        Ad = [set() for _ in range(n)]
        for u, v in E: Ad[u].add(v); Ad[v].add(u)
        for c in (c1, c2):
            if len(Ad[c]) == 2:
                y, z = sorted(Ad[c])
                if z not in Ad[y]: res['C2'] = True
        if not res['C3']:
            if static_steer(n, E, c1, c2) or static_steer(n, E, c2, c1): res['C3'] = True
        if res['C2'] and res['C3']: break
    return inst, res

if __name__ == '__main__':
    C = collections.Counter(); resid = []
    with Pool(4) as pool:
        for r in pool.imap_unordered(work, open('pall8.out'), chunksize=20):
            if r is None: continue
            inst, res = r
            C['joint'] += 1
            for k in res: C[k] += res[k]
            u = res['C1'] or res['C2'] or res['C3']
            C['union'] += u
            if not u: resid.append(inst)
    for k in sorted(C): print(k, C[k])
    open('resid_C123_8.txt', 'w').write('\n'.join(resid) + '\n')

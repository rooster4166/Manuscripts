"""allcov.py -- union coverage of the proved sufficient conditions for L_N(2) on the order-8 data:
  B   Corollary B (ln, Lean): some c_i is a leaf, a_i not in N[stem], no vertex adjacent to a_1 and a_2
  C1  joint path P (c1-c2 path avoiding a1,a2) and some d(c_i) = 1
  C2  joint P and c_i of degree 2 in K0 = F - E(P) with non-adjacent neighbours (suppression)
  C3  joint P and Lemma S (static steering of one token) in K0
  G   cut-vertex gluing (G1-G3)"""
import sys, collections
from multiprocessing import Pool
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
from cov import static_steer, ekey
def comp(adj, s, banned):
    seen = {s}; st = [s]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen and v not in banned: seen.add(v); st.append(v)
    return seen
def gluing(adj, ci, ai, cj, aj):
    """Theorem G: v = a_j a cut vertex, B = component of c_j in F - v, c_i not in B, and
    (G1) a_i not in B, or (G2) d_B(v) odd, or (G3) c_i not adjacent to v, or the component of c_i
    in F - v contains a vertex not adjacent to v (NA's boundary)."""
    v = aj; B = comp(adj, cj, {v})
    if ci in B: return False
    if ai not in B: return True
    if len(adj[v] & B) % 2 == 1: return True
    if ci not in adj[v]: return True
    return any(x not in adj[v] for x in comp(adj, ci, {v}))
def corB(adj, c1, a1, c2, a2):
    if any(x in adj[a1] and x in adj[a2] for x in range(len(adj))): return False
    for ci, ai in ((c1, a1), (c2, a2)):
        if len(adj[ci]) == 1:
            w = next(iter(adj[ci]))
            if ai != w and ai not in adj[w]: return True
    return False
def work(line):
    inst, rest = line.split(' | ')
    t = inst.split(); n, adj = g6_decode(t[0]); c1,a1,c2,a2 = map(int,t[1:5])
    E0 = frozenset(ekey(u, v) for u in range(n) for v in adj[u])
    A = [tuple(map(int,r.split(':')[1].split('-'))) for r in rest.split() if r.split(':')[2]=='a' and r.split(':')[0]=='0']
    f = {'B': corB(adj, c1, a1, c2, a2), 'C1': False, 'C2': False, 'C3': False,
         'G': (not A) and (gluing(adj, c1, a1, c2, a2) or gluing(adj, c2, a2, c1, a1))}
    if A:
        f['C1'] = len(adj[c1]) == 1 or len(adj[c2]) == 1
        for P in A:
            E = E0 - set(ekey(p, q) for p, q in zip(P, P[1:]))
            Ad = [set() for _ in range(n)]
            for u, v in E: Ad[u].add(v); Ad[v].add(u)
            for c in (c1, c2):
                if len(Ad[c]) == 2:
                    y, z = sorted(Ad[c])
                    if z not in Ad[y]: f['C2'] = True
            if not f['C3'] and not f['C1']:
                if static_steer(n, E, c1, c2) or static_steer(n, E, c2, c1): f['C3'] = True
            if f['C2'] and (f['C3'] or f['C1']): break
    return inst, bool(A), f
if __name__ == '__main__':
    C = collections.Counter(); resid = []
    with Pool(4) as pool:
        for inst, joint, f in pool.imap_unordered(work, open(sys.argv[1]), chunksize=20):
            C['inst'] += 1; C['joint' if joint else 'sep'] += 1
            for k in f: C[k] += f[k]
            u = any(f.values()); C['union'] += u
            if not u: resid.append(inst + (' J' if joint else ' S'))
    for k in sorted(C): print(k, C[k])
    open(sys.argv[2], 'w').write('\n'.join(sorted(resid)) + '\n')
    print('residual', len(resid))

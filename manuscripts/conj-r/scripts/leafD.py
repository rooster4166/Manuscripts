"""leafD.py -- separated residual with c_i a leaf at a_j: (i) exact 'avoid the even vertex':
F' = F - c_i has the single even vertex g = a_j; is there a Lovasz decomposition of F' with
g not on Q(c_j)?  (ii) static steering of the g-token in F' + c_j l avoiding N[c_j] and g."""
import sys, collections, subprocess
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode, g6_encode
from cov import ekey
def steer_avoid(n, E, g, X):
    seen = set()
    def rec(p, E):
        if (p, E) in seen: return False
        seen.add((p, E))
        Ad = [set() for _ in range(n)]
        for u, v in E: Ad[u].add(v); Ad[v].add(u)
        for u in Ad[p]:
            if u in X: continue
            if len(Ad[u]) == 1: return True
            if rec(u, E - {ekey(p, u)}): return True
        return False
    return rec(g, E)
C = collections.Counter(); Q = []; meta = []
for l in open('resid_all8.txt'):
    t = l.split()
    if not t or t[-1] != 'S': continue
    n, adj = g6_decode(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
    done = False
    for (ci, ai, cj, aj) in ((c1, a1, c2, a2), (c2, a2, c1, a1)):
        if len(adj[ci]) == 1 and aj in adj[ci]:
            A2 = [set(a) for a in adj]; A2[ci].discard(aj); A2[aj].discard(ci)
            Q.append(g6_encode(n, A2) + ' A %d %d' % (cj, aj)); meta.append(l.strip())
            # static steering in F' + c_j l (l = n)
            E = frozenset(ekey(u, v) for u in range(n) for v in A2[u]) | {(cj, n)}
            X = A2[cj] | {cj, n, aj}
            if steer_avoid(n + 1, E, aj, X): C['steer'] += 1; done = True
            break
    if not done: C['nosteer'] += 1
out = subprocess.run(['./lnsolve3'], input='\n'.join(Q) + '\n', capture_output=True, text=True).stdout.split('\n')
print('leaf-at-a_j instances', len(Q), collections.Counter(o.split()[0] for o in out if o))
print(dict(C))

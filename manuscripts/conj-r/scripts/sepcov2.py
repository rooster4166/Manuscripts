"""sepcov2.py -- separated instances: coverage of the cut-vertex gluing theorem (G1-G3).
v = a_j a cut vertex separating c_j from c_i; B = component of c_j in F - v, A = the rest.
(G1) a_i in A; (G2) a_i in B and d_B(v) odd; (G3) a_i in B, d_B(v) even and c_i not adjacent to v."""
import sys, collections
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
def comp(adj, s, banned):
    seen = {s}; st = [s]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen and v not in banned: seen.add(v); st.append(v)
    return seen
def gluing(adj, ci, ai, cj, aj):
    v = aj
    B = comp(adj, cj, {v})
    if ci in B: return None
    if ai not in B: return 'G1'
    dB = len(adj[v] & B)
    if dB % 2 == 1: return 'G2'
    if ci not in adj[v]: return 'G3'
    return 'G4'
C = collections.Counter(); resid = []
for line in open(sys.argv[1]):
    t = line.split(); n, adj = g6_decode(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
    C['sep'] += 1
    r = [gluing(adj, c1, a1, c2, a2), gluing(adj, c2, a2, c1, a1)]
    r = [x for x in r if x]
    if not r: C['2cut'] += 1; resid.append(line.strip() + ' 2cut'); continue
    best = min(r)
    C[best] += 1
    if best == 'G4': resid.append(line.strip() + ' G4')
print(dict(C))
open(sys.argv[2], 'w').write('\n'.join(resid) + '\n')

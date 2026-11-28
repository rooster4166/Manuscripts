"""sepcls.py -- classify separated instances: B (Corollary B), G (gluing G1-G3), G4 leaf (c_i a leaf
at a_j), G4 other, 2cut.  Writes the G4-leaf instances (for the avoid-the-even-vertex test) and the
rest of the residual."""
import sys, collections
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
from allcov import comp, gluing, corB
C = collections.Counter()
fl = open(sys.argv[2], 'w'); fo = open(sys.argv[3], 'w')
for line in open(sys.argv[1]):
    t = line.split()
    if not t: continue
    n, adj = g6_decode(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
    C['sep'] += 1
    if corB(adj, c1, a1, c2, a2): C['B'] += 1; continue
    if gluing(adj, c1, a1, c2, a2) or gluing(adj, c2, a2, c1, a1): C['G'] += 1; continue
    leaf = None
    for (ci, ai, cj, aj) in ((c1, a1, c2, a2), (c2, a2, c1, a1)):
        if len(adj[ci]) == 1 and aj in adj[ci] and ci not in comp(adj, cj, {aj}):
            leaf = (ci, ai, cj, aj); break
    cut = any(c2 not in comp(adj, c1, {x}) for x in (a1, a2))
    if leaf: C['G4leaf'] += 1; fl.write(line.strip() + ' %d %d %d %d\n' % leaf)
    elif cut: C['G4other'] += 1; fo.write(line.strip() + ' G4\n')
    else: C['2cut'] += 1; fo.write(line.strip() + ' 2cut\n')
print(dict(C))

"""g3p.py -- the G4other separated instances: does the NA boundary condition give (G3')?
v = a_j cut vertex, B = component of c_j in F - v (contains a_i), A = rest (contains c_i), c_i ~ v,
d_B(v) even.  (G3'): the component of c_i in F_A - v contains a vertex not adjacent to v."""
import sys, collections
sys.path.insert(0, '/home/user/Manuscripts/manuscripts/ln/scripts')
from lnlib import g6_decode
def comp(adj, s, banned):
    seen = {s}; st = [s]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen and v not in banned: seen.add(v); st.append(v)
    return seen
C = collections.Counter()
for line in open(sys.argv[1]):
    t = line.split()
    if not t or t[-1] != 'G4': continue
    n, adj = g6_decode(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
    ok = False
    for (ci, ai, cj, aj) in ((c1, a1, c2, a2), (c2, a2, c1, a1)):
        v = aj; B = comp(adj, cj, {v})
        if ci in B: continue
        Cc = comp(adj, ci, {v})        # component of c_i in F - v (inside A)
        if any(x not in adj[v] for x in Cc): ok = True
    C['G3prime' if ok else 'not'] += 1
print(dict(C))

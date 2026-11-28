"""A42: compare the residual of jcov (own code) with data/residual_order*.txt, and classify it."""
import sys, collections
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import g6dec, comp_of
mine = {}
for l in open(sys.argv[1]):
    a, b = l.split(' | '); f = b.split()
    if not any(int(x) for x in f[2:]): mine[a.strip()] = f[0]
ref = {}
for l in open(sys.argv[2]):
    t = l.split()
    if t: ref[' '.join(t[:5])] = t[5]
print('residual: mine', len(mine), 'data file', len(ref), 'identical sets:', set(mine) == set(ref),
      'same J/S labels:', all(mine[k] == ref.get(k) for k in mine))
C = collections.Counter(); EJ = []
for k, typ in mine.items():
    t = k.split(); n, adj = g6dec(t[0]); c1, a1, c2, a2 = map(int, t[1:5]); m = sum(map(len, adj)) // 2
    if typ == 'J': C['joined'] += 1; EJ.append(m); continue
    leaf = (len(adj[c1]) == 1 and a2 in adj[c1]) or (len(adj[c2]) == 1 and a1 in adj[c2])
    cut = c2 not in comp_of(adj, c1, {a1}) or c2 not in comp_of(adj, c1, {a2})
    C['leaf at head' if leaf else ('cut' if cut else '2cut')] += 1
print(dict(C))
if EJ: print('joined residual |E|: min', min(EJ), 'max', max(EJ), '#|E|>=16', sum(e >= 16 for e in EJ), 'by |E|', sorted(collections.Counter(EJ).items()))

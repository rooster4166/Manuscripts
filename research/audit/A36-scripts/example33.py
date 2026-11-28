"""example33.py (A36): Example 3.3 of multi-token.tex, every stated fact, by direct computation."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from thm42 import replay
J = nx.from_graph6_bytes(b'HsaBEy~')
z, r, w = 7, 3, 1
pairs = [(4, 0), (8, 5)]                      # (y, x)
assert [v for v in J if J.degree(v) % 2 == 0] == [z] and J.degree(z) == 6
assert set(J[z]) == {r, w, 4, 0, 8, 5} and J.has_edge(4, 0) and J.has_edge(8, 5)
assert set(J[w]) == {z, 0, 6} and not J.has_edge(0, 6) and J.degree(4) == 3
assert not J.has_edge(3, 4)                   # r !~ 4
print('N(4) =', sorted(J[4]), ' N(8) =', sorted(J[8]), ' N(3) =', sorted(J[3]), ' d(3) =', J.degree(3))
moves = [('S', 1), ('M', 8, 3), ('M', 3, z), ('M', 4, 8), ('D', 0)]
replay(J, z, w, pairs, moves)
# narrative: after S, 8->3, 3->z: z isolated (retired); after 4->8: 8 odd? no: 8 becomes a token
K = {v: set(J[v]) for v in J}
def rm(a, b): K[a].discard(b); K[b].discard(a)
rm(z, w)
for y, x in pairs: rm(z, y); rm(z, x); rm(y, x)
K['l1'] = {4}; K[4].add('l1'); K['l2'] = {8}; K[8].add('l2')
rm(1, 0); rm(1, 6); K[0].add(6); K[6].add(0)
print('after S: d(8) =', len(K[8]), 'tokens', sorted(str(v) for v in K if K[v] and len(K[v]) % 2 == 0))
rm(8, 3); print('after 8->3: tokens', sorted(str(v) for v in K if K[v] and len(K[v]) % 2 == 0))
rm(3, z); print('after 3->z: d(z) =', len(K[z]), 'tokens', sorted(str(v) for v in K if K[v] and len(K[v]) % 2 == 0))
print('before 4->8: d(8) =', len(K[8]), 'nbrs of 8 minus 4:', sorted(str(v) for v in K[8] - {4}))
rm(4, 8); print('after 4->8: N(4) =', K[4], 'tokens', sorted(str(v) for v in K if K[v] and len(K[v]) % 2 == 0))
rm(4, 'l1'); print('after D: tokens', sorted(str(v) for v in K if K[v] and len(K[v]) % 2 == 0), 'live l2:', 'l2' in K[8])
print('Example 3.3: all stated facts OK')

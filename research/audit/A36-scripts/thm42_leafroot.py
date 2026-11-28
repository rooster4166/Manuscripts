"""thm42_leafroot.py (A36): Theorem 4.2's hypotheses (A1)+(B2) hold at a root r of degree 1, where
Test1 fails (r is isolated in J - z), although the theorem's conclusion says Test1 holds.
Labels are those of the graph6 string."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from thm42 import certificates, replay
J = nx.from_graph6_bytes(b'Lsech?H?GA_B?@')
z, r, w, P1, P2 = 0, 1, 2, (4, 3), (6, 5)            # (y1, x1), (y2, x2)
assert [v for v in J if J.degree(v) % 2 == 0] == [z] and J.degree(z) == 6 and J.degree(r) == 1
for v in (w, 4, 8):
    print('N(%d) =' % v, sorted(J[v]))
print('5 ~ 7:', J.has_edge(5, 7), ' 7 ~ 9:', J.has_edge(7, 9), ' 8 ~ 6:', J.has_edge(8, 6), ' kappa =', nx.node_connectivity(J))
certs = list(certificates(J, z, r, w, P1, P2))
print('certificates (kind, schedule):', certs)
for kind, mv in certs:
    replay(J, z, w, [P1, P2], mv)
print('legal and terminal: Theorem 4.2 applies at r = 1 with d(r) = 1; r is isolated in J - z, so no',
      'decomposition of J - z has 2 ends at r and Test1 fails at (J, z, r).')

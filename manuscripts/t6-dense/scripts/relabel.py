"""relabel.py: put the six even vertices of B = J - z first (U = {0..5}) and keep the graphs whose
core D = K6 - B[U] is one of the dense residual shapes (or all, with ALL=1).
usage: relabel.py [ALL] < g6 > g6"""
import sys
import networkx as nx
sys.path.insert(0, __import__('os').path.dirname(__file__))
from dense import shape

keep_all = len(sys.argv) > 1 and sys.argv[1] == '1'
cnt = {}
for line in sys.stdin:
    line = line.strip().split()[0] if line.strip() else ''
    if not line:
        continue
    B = nx.from_graph6_bytes(line.encode())
    U = [v for v in B if B.degree(v) % 2 == 0]
    if len(U) != 6:
        continue
    order = U + [v for v in B if v not in U]
    pos = {v: i for i, v in enumerate(order)}
    B2 = nx.Graph()
    B2.add_nodes_from(range(len(order)))          # graph6 follows insertion order
    B2.add_edges_from((pos[a], pos[b]) for a, b in B.edges())
    sh, _ = shape(B2)
    cnt[sh] = cnt.get(sh, 0) + 1
    if keep_all or sh != 'other':
        print(nx.to_graph6_bytes(B2, header=False).decode().strip())
print('#', cnt, file=sys.stderr)

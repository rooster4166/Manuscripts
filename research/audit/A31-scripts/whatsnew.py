"""whatsnew.py: Remark 3.4 family B = {r, s} joined to all of a 4-regular H (r, s non-adjacent).
Prints graph6 lines 'g6 r' for lovcheck, and checks degrees, 2-connectivity, the literature classes
(own code + networkx planarity), (**) at r and s, and the number of degree-(n-2) vertices."""
import random
import sys

import networkx as nx

sys.path.insert(0, __import__("os").path.dirname(__file__))
from g6 import to_g6, two_connected, degenerate_at_most, is_forest  # noqa: E402
from recount_conditions import star2  # noqa: E402

out = open(sys.argv[1], "w")
rng = random.Random(31)
Hs = [("C8(1,2)", nx.circulant_graph(8, [1, 2]))]
for m in (10, 12, 14):
    Hs.append(("rand4reg%d" % m, nx.random_regular_graph(4, m, seed=rng.randrange(1 << 30))))
for name, H in Hs:
    H = nx.convert_node_labels_to_integers(H)
    h = H.number_of_nodes()
    n = h + 2
    r, s = h, h + 1
    adj = [set(H[v]) for v in range(h)] + [set(range(h)), set(range(h))]
    for v in range(h):
        adj[v] |= {r, s}
    deg = [len(a) for a in adj]
    B = nx.Graph([(v, w) for v in range(n) for w in adj[v] if v < w])
    lit = (nx.check_planarity(B)[0], max(deg) <= 4,
           max(len(adj[v] - {r}) for v in range(n) if v != r) <= 3,
           degenerate_at_most(n, adj, 2), degenerate_at_most(n, adj, 3), is_forest(set(range(n)) - {r}, adj))
    print(name, "n=%d degrees %s 2conn %s" % (n, sorted(set(deg)), two_connected(n, adj)),
          "planar/D<=4/D(B-r)<=3/2-degen/3-degen(=>tw<=3 necessary)/B-r forest:", lit,
          "m=%d 3n-6=%d" % (B.number_of_edges(), 3 * n - 6),
          "(**) at r, s:", star2(n, adj, r), star2(n, adj, s), "#deg n-2:", deg.count(n - 2))
    if n <= 12:
        out.write("%s %d\n%s %d\n" % (to_g6(n, adj), r, to_g6(n, adj), s))

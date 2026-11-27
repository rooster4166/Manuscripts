"""Among all away edges (x, y) (x odd, d(x)>=3, y != z), compare PEE failure with N[x]-blocking."""
import sys, collections
import networkx as nx
from block_check import blocked
C = collections.Counter()
for line in sys.stdin:
    if not line.startswith("G "): continue
    p = line.split(); G = nx.from_graph6_bytes(p[1].encode()); z = int(p[2][2:])
    for tok in p[3:]:
        if '-' not in tok: continue
        xy, r = tok.split(':'); x, y = map(int, xy.split('-'))
        b = blocked(G, z, x, y)
        C[(('blocked' if b else 'unblocked'), ('fail' if r == '0' else 'ok'))] += 1
print(dict(C))

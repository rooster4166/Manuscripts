import sys, networkx as nx, collections
C = collections.Counter()
for l in open(sys.argv[1]):
    if not l.startswith('NOREC'): continue
    p = l.split(); G = nx.from_graph6_bytes(p[1].encode()); g = int(p[2][2:]); c = int(p[3][2:])
    C[(G.degree(c), G.degree(g) if g >= 0 else 0, p[-1])] += 1
for k, v in sorted(C.items()): print(k, v)

import sys, itertools
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from pathnum import solve, verify_partition
from seglib import *
h = 8
E = (0,3,4,7,6,1,2,5)
segs = segments(h, E, 'path')
cls = classes(segs)
print("segments", segs); print("classes", [[ (i, segs[i]) for i in c] for c in cls])
for ch in itertools.product(*cls):
    S = frozenset(ch)
    n, edges = graph(h, segs, S)
    G = nx.Graph(); G.add_edges_from(edges)
    assert G.number_of_edges() == len(edges)
    r = solve(G, budget=2, workers=1)
    ok = r.status in ('OPTIMAL','FEASIBLE') and r.value <= 2
    print(sorted(S), [segs[i] for i in sorted(S)], "pathnum:", r.status, r.value, r.paths if ok else '', "verified" if ok and verify_partition(G, r.paths) else '')

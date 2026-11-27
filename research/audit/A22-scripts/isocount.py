"""isocount.py N: number of isomorphism classes of pairs (G, F), G connected all-odd of order N, F a
2-matching, by orbit counting under Aut(G) (automorphisms by networkx VF2).  Independent of the
encode.c / labelg / decode.py pipeline.  Also checks decode(iso file) round trip for N = 8."""
import sys, itertools, subprocess
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

N = int(sys.argv[1])
g6s = subprocess.run(['nauty-geng', '-cq', str(N)], capture_output=True, text=True).stdout.split()
total = classes = 0
for s in g6s:
    G = nx.from_graph6_bytes(s.encode())
    if any(d % 2 == 0 for _, d in G.degree()):
        continue
    E = [tuple(sorted(e)) for e in G.edges()]
    M2 = [frozenset((frozenset(e), frozenset(f))) for e, f in itertools.combinations(E, 2) if not set(e) & set(f)]
    total += len(M2)
    auts = list(GraphMatcher(G, G).isomorphisms_iter())
    seen = set()
    for F in M2:
        if F in seen:
            continue
        classes += 1
        for p in auts:
            seen.add(frozenset(frozenset(p[v] for v in e) for e in F))
print('N=%d instances=%d classes=%d' % (N, total, classes))

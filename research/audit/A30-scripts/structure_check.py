"""A30 audit: structural claims of Section 5 on all connected Eulerian graphs of order 4..10.
 - Prop 5.4: for an ear v (N(v)={a,b}, ab in E) with B-v-ab disconnected: B-v connected, exactly two
   components, a and b separated, each component Eulerian and of order 1 or >= 3.
 - Prop 5.5: twins u,v of degree 2 with N={a,b} and ab in E: B-u-v connected, Eulerian, >= 3 vertices.
 - Lemma 5.1: v of degree 2 with ab not in E: B/v simple connected Eulerian on n-1 vertices."""
import sys, itertools
from collections import Counter
import networkx as nx

cnt = Counter()
for fn in sys.argv[1:]:
    for l in open(fn):
        B = nx.from_graph6_bytes(l.strip().encode()); n = B.number_of_nodes()
        deg2 = [v for v in B if B.degree(v) == 2]
        for v in deg2:
            a, b = B[v]
            if B.has_edge(a, b):
                H = B.copy(); H.remove_node(v)
                assert nx.is_connected(H)
                H.remove_edge(a, b)
                if not nx.is_connected(H):
                    comps = list(nx.connected_components(H))
                    assert len(comps) == 2 and not any(a in c and b in c for c in comps)
                    for c in comps:
                        S = H.subgraph(c)
                        assert len(c) == 1 or len(c) >= 3
                        assert all(d % 2 == 0 for _, d in S.degree())
                    cnt['ear-at-cut'] += 1
                else:
                    cnt['ear-connected'] += 1
            else:
                H = B.copy(); H.remove_node(v); H.add_edge(a, b)
                assert nx.is_connected(H) and all(d % 2 == 0 for _, d in H.degree()) and H.number_of_nodes() == n - 1
                cnt['suppressible'] += 1
        for u, v in itertools.combinations(deg2, 2):
            if set(B[u]) == set(B[v]):
                a, b = B[u]
                if B.has_edge(a, b):
                    H = B.copy(); H.remove_nodes_from([u, v])
                    assert nx.is_connected(H) and H.number_of_nodes() >= 3 and all(d % 2 == 0 for _, d in H.degree())
                    cnt['twin-ab-edge'] += 1
                else:
                    cnt['twin-ab-nonedge'] += 1
print(dict(cnt))

import itertools, time, networkx as nx
from circ import ham_decomp, check
n = 13; k = 6
H = nx.Graph(); H.add_nodes_from(range(n)); H.add_edges_from([(0,1),(0,2),(0,3),(4,5),(6,7)])  # K_{1,3} + 2K_2, m=5, L=1
G = nx.complete_graph(n); G.remove_edges_from(H.edges())
# orbits of edges of G under Aut(H)
GM = nx.algorithms.isomorphism.GraphMatcher(H, H)
auts = list(GM.isomorphisms_iter())
orb = {}
for e in G.edges():
    key = min(tuple(sorted((a[e[0]], a[e[1]]))) for a in auts)
    orb.setdefault(key, e)
print("edge orbits of G under Aut(H):", len(orb), flush=True)
t0 = time.time(); ok = 0
for key, Q in orb.items():
    X = list(H.edges()) + [Q]
    st, cyc = ham_decomp(n, [[e] for e in X], time_limit=900)
    good = cyc is not None and check(n, cyc, [[e] for e in X])
    # open and verify k+1 paths partition G
    if good:
        paths = []
        for c, e in enumerate(X):
            cy = cyc[c]; i = cy.index(e[0])
            if cy[(i + 1) % n] == e[1]: paths.append([cy[(i + 1 + j) % n] for j in range(n)])
            else: paths.append([cy[(i - 1 - j) % n] for j in range(n)])
        paths = paths[:5] + [paths[5]]  # all opened
        seen = set()
        allp = [p for p in paths] + [list(Q)]
        for P in allp:
            for a, b in zip(P, P[1:]):
                f = frozenset((a, b)); assert G.has_edge(a, b) and f not in seen; seen.add(f)
        assert len(seen) == G.number_of_edges() and len(allp) == k + 1
    ok += good
    print("Q", Q, st, "verified" if good else "NOT FOUND", f"{time.time()-t0:.0f}s", flush=True)
print(f"n=13 residual H=K13+2K2: {ok}/{len(orb)} plant orbits completed to 7-path partitions", flush=True)

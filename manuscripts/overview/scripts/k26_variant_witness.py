"""Witness for the all-odd lift at a hub r of the cone over K_{2,6}, with r a child of Phi having
two children: a Lovasz decomposition D0 of H = B - Phi with (i), (ii), its forest-stepping lift, and
an independent check that the lift decomposes B = K_{2,6} into 4 paths with >= 2 ends at r."""
import networkx as nx
from converses import decomps, tjoin_forests, rootings, base_ok, append_forest, is_decomp, ends_of, terminal_ok
B = nx.complete_bipartite_graph(2, 6); r = 0
for Phi in tjoin_forests(B, list(B.nodes())):
    for par in rootings(Phi):
        if r not in par or sum(1 for v in par if par[v] == r) < 2: continue
        H = B.copy(); H.remove_edges_from(Phi)
        for D0 in decomps(H, 10**9, {v: H.degree(v) % 2 for v in H}):
            if not base_ok(D0, par): continue
            D1 = append_forest(D0, par)
            assert is_decomp(B, D1) and len(D1) <= 4 and ends_of(D1, r) >= 2 and terminal_ok(D1, par)
            # independent re-check of the lifted decomposition
            E = set()
            for p in D1:
                assert len(set(p)) == len(p)
                for i in range(len(p) - 1):
                    e = frozenset(p[i:i+2]); assert B.has_edge(*p[i:i+2]) and e not in E; E.add(e)
            assert len(E) == B.number_of_edges()
            print('Phi (child, parent):', sorted(par.items()))
            print('H = B - Phi edges:', sorted(tuple(sorted(e)) for e in H.edges()))
            print('D0 (Lovasz, H):', D0)
            print('lift (decomposition of K_{2,6}):', D1, '| paths', len(D1), '| ends at r =', ends_of(D1, r))
            raise SystemExit

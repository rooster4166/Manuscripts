"""The all-odd (T1) lift on the cone over K_{2,6} (synthesis section 31, caveat): is there a forest
N(z)-join Phi of B = K_{2,6} (here N(z) = V(B), so every vertex has odd Phi-degree), rooted with the
root r a root of Phi, such that H = B - Phi has a base?  By the converse (overview Prop. 3.8) this is
the same as: B has a decomposition into at most 4 paths with Phi terminal at parents.  We test the
base condition directly on H, exhaustively, and also the converse form, at a hub and at a leaf."""
import itertools
import networkx as nx
from converses import decomps, tjoin_forests, rootings, base_ok, terminal_ok, ends_of
B = nx.complete_bipartite_graph(2, 6)          # hubs 0, 1; leaves 2..7
T = list(B.nodes()); k = 4
forests = tjoin_forests(B, T)
print('forest V(B)-joins of K_{2,6}:', len(forests))
DB = decomps(B, k)                                      # all decompositions of B into <= 4 paths
print('decompositions of K_{2,6} into <= 4 paths:', len(DB))
for r in (0, 2):
    found_a = found_b = False; tried = 0
    for Phi in forests:
        for par in rootings(Phi, must_root=r):
            tried += 1
            H = B.copy(); H.remove_edges_from(Phi)
            L = decomps(H, 10**9, {v: H.degree(v) % 2 for v in H})
            a = any(base_ok(D, par) for D in L)
            b = any(terminal_ok(D, par) for D in DB)
            assert a == b
            found_a |= a
    print('root', r, '(hub)' if r < 2 else '(leaf)', 'rooted forests tried', tried, 'all-odd base exists:', found_a)
# (T1) itself at a hub: B has <= 4 paths with >= 2 ends at the hub (known true: K_{2,6} is planar)
print('(T1) at hub 0:', any(ends_of(D, 0) >= 2 for D in DB))
# Variant: r a child of Phi with at least two children (ends at r = c(r) >= 2 after the lift).
for r in (0,):
    found = False; tried = 0
    for Phi in forests:
        for par in rootings(Phi):
            if r not in par or sum(1 for v in par if par[v] == r) < 2: continue
            tried += 1
            if any(terminal_ok(D, par) for D in DB): found = True
    print('variant, root', r, 'as a child with >= 2 children: rooted forests tried', tried, 'base exists:', found)

"""The all-odd (T1) lift at every root of HsaAD~} (direct-test1 Example 4.7: one root has no forest
base), for both variants: r a root of Phi, and r a child of Phi with >= 2 children.  Uses the
converse form (overview Prop. 3.8): a base exists iff J - z has <= k paths with Phi terminal at parents."""
import networkx as nx
from converses import decomps, tjoin_forests, rootings, terminal_ok, ends_of
J = nx.from_graph6_bytes(b'HsaAD~}')
ev = [v for v in J if J.degree(v) % 2 == 0]; assert len(ev) == 1
z = ev[0]; B = J.copy(); B.remove_node(z); k = (J.number_of_nodes() - 1) // 2
Nz = sorted(J.neighbors(z))
print('z =', z, 'd(z) =', J.degree(z), 'N(z) =', Nz, 'k =', k, 'edges of B:', B.number_of_edges(), 'kappa(J) =', nx.node_connectivity(J))
DB = decomps(B, k); print('decompositions of J - z into <= k paths:', len(DB))
forests = tjoin_forests(B, Nz); print('forest N(z)-joins:', len(forests))
for r in Nz:
    root_ok = child_ok = False
    for Phi in forests:
        for par in rootings(Phi):
            if r in par and sum(1 for v in par if par[v] == r) < 2: continue
            if any(terminal_ok(D, par) for D in DB):
                if r in par: child_ok = True
                else: root_ok = True
        if root_ok and child_ok: break
    t1 = any(ends_of(D, r) >= 2 for D in DB)
    print('root', r, 'd(r) =', J.degree(r), '| base with r a root:', root_ok, '| with r a child:', child_ok, '| (T1):', t1)

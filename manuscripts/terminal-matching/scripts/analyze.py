"""Summarise failure lines of ptm: connectivity of J = G' + z V(F), of G' and of G = G' + F (multigraph)."""
import sys, collections
import networkx as nx
c = collections.Counter(); ex = {}
for line in open(sys.argv[1]):
    t = line.split()
    if t[0] not in ('PTMFAIL', 'RFAIL'): continue
    Gp = nx.from_graph6_bytes(t[1].encode()); n = Gp.number_of_nodes()
    pairs = [tuple(map(int, x.rstrip('*').split('-'))) for x in t[2:] if '-' in x and not x.startswith('end')]
    J = Gp.copy(); z = n; J.add_node(z); J.add_edges_from((z, v) for p in pairs for v in p)
    kJ = nx.node_connectivity(J); kG = nx.node_connectivity(Gp) if n > 1 else 0
    npar = sum(1 for a, b in pairs if Gp.has_edge(a, b))
    key = (t[0], len(pairs), npar, 'kJ=%d' % kJ, 'kGp=%d' % kG)
    c[key] += 1
    ex.setdefault(key, line.strip())
for k, v in sorted(c.items()): print(k, v, '  e.g.', ex[k])

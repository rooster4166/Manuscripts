"""frozen.py: the frozen roots of degree < n-2 (multi-token: least potential 5 in *_explore.txt).
usage: frozen.py   (run from scripts/; writes ../data/frozen9.txt (graph6 of J, root) and
../data/Jfrozen_{resid_O8,resid_O10,e28_hard}.txt (graph6 of J = B + z, root))."""
import networkx as nx
R = '../../multi-token/data/runs/'
def parse(fn, resid):
    out = []
    for line in open(R + fn):
        f = line.split()
        if not f or f[0] != 'ROOT': continue
        g6 = f[1]; r = int(f[2][2:])
        mp = int([x for x in f if x.startswith('min_phi')][0].split('=')[1])
        G = nx.from_graph6_bytes(g6.encode())
        if resid:
            nB = G.number_of_nodes(); J = G.copy(); J.add_node(nB); [J.add_edge(nB, u) for u in range(6)]
            g6J = nx.to_graph6_bytes(J, header=False).decode().strip()
        else:
            J = G; g6J = g6
        n = J.number_of_nodes()
        if mp == 5 and J.degree(r) < n - 2: out.append('%s %d' % (g6J, r))
    return out
o = parse('J9_explore.txt', False)
open('../data/frozen9.txt', 'w').write('\n'.join(o) + '\n'); print('order 9', len(o))
for f in ('resid_O8', 'resid_O10', 'e28_hard'):
    o = parse(f + '_explore.txt', True)
    open('../data/Jfrozen_%s.txt' % f, 'w').write('\n'.join(o) + '\n'); print(f, len(o))

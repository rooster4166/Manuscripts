"""A20: pairs (J, r) with J - z disconnected, n <= 7: how many satisfy STL and T1 (own enumerator)."""
import networkx as nx
from pdec import Graph, stl, test1
SCR = '/home/user/Manuscripts/manuscripts/stl/scripts/'
for n in (5, 7):
    c = dict(disc_pairs=0, disc_dr3=0, disc_dr3_stl=0, disc_dr3_t1=0, disc_dr1=0, disc_dr1_stl=0)
    ex = None
    for l in open(SCR + 'one_even_%d.g6' % n, 'rb'):
        J = nx.from_graph6_bytes(l.strip())
        ev = [v for v in J if J.degree(v) % 2 == 0]
        if len(ev) != 1 or J.degree(ev[0]) == 0:
            continue
        z = ev[0]
        H = J.copy(); H.remove_node(z)
        if nx.is_connected(H):
            continue
        g = Graph(J)
        for r in J[z]:
            c['disc_pairs'] += 1
            s = stl(g, g.lab[z], g.lab[r])
            if J.degree(r) >= 3:
                c['disc_dr3'] += 1
                c['disc_dr3_stl'] += s
                t = test1(J, z, r)
                c['disc_dr3_t1'] += t
                if s and ex is None:
                    ex = (l.strip().decode(), z, r, sorted(len(x) for x in nx.connected_components(H)))
            else:
                c['disc_dr1'] += 1
                c['disc_dr1_stl'] += s
    print(n, c, 'example J-z disconnected, d(r)>=3, STL true:', ex)

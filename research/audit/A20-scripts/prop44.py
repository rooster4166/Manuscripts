"""A20: check Proposition 4.4 (pairing <=> terminal matching in G = (J - z) + M) on all one-even
graphs of order 5 and 7 and every perfect matching M of N(z) with no pair adjacent in J."""
import networkx as nx
from pdec import Graph, pairing, perfect_matchings, search, lovasz_prof
SCR = '/home/user/Manuscripts/manuscripts/stl/scripts/'


def ptm(G, F):
    g = Graph(G)
    Fl = {frozenset((g.lab[a], g.lab[b])) for (a, b) in F}
    def step(acc, inf, path):
        es = [frozenset((path[i], path[i + 1])) for i in range(len(path) - 1)]
        idx = [i for i, e in enumerate(es) if e in Fl]
        if len(idx) >= 2:
            return None
        if len(idx) == 1 and idx[0] not in (0, len(es) - 1):
            return None
        return acc
    return search(g, lovasz_prof(g), step=step, acc0=0)


for n in (5, 7):
    agree = dis = tot = 0
    for l in open(SCR + 'one_even_%d.g6' % n, 'rb'):
        J = nx.from_graph6_bytes(l.strip())
        ev = [v for v in J if J.degree(v) % 2 == 0]
        if len(ev) != 1 or J.degree(ev[0]) == 0:
            continue
        z = ev[0]
        g = Graph(J)
        N = sorted(J[z])
        for M in perfect_matchings(N):
            pairs = [tuple(p) for p in M]
            if any(J.has_edge(a, b) for (a, b) in pairs):
                continue
            tot += 1
            a = pairing(g, g.lab[z], {frozenset((g.lab[x], g.lab[y])) for (x, y) in pairs})
            G = J.copy(); G.remove_node(z); G.add_edges_from(pairs)
            assert all(d % 2 == 1 for _, d in G.degree())
            b = ptm(G, pairs)
            if a == b:
                agree += 1
            else:
                dis += 1; print('DISAGREE', l.strip().decode(), pairs, a, b)
    print('n =', n, 'non-adjacent pairings', tot, 'agree', agree, 'disagree', dis)

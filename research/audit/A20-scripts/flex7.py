"""A20: EE / STS / HALF / PAIR on the 3-connected one-even graphs of order 5 and 7 (own enumerator)."""
import sys, itertools, json
import networkx as nx
from pdec import Graph, short_at, pairing, perfect_matchings, search, lovasz_prof

SCR = '/home/user/Manuscripts/manuscripts/stl/scripts/'


def half(g, z, S):
    def step(acc, inf, path):
        if inf is None:
            return acc
        a, sa, b, sb = inf
        if (a in S) != sa or (b in S) != sb:
            return None
        return acc
    return search(g, lovasz_prof(g), z=z, star=True, step=step, acc0=0)


for n in (5, 7):
    c = dict(graphs=0, EE=0, STS=0, EEn=0, HALF=0, HALFn=0, PAIR=0, PAIRn=0, lovasz_all=0)
    pairfails = []
    for l in open(SCR + 'one_even_%d.g6' % n, 'rb'):
        l = l.strip()
        J = nx.from_graph6_bytes(l)
        ev = [v for v in J if J.degree(v) % 2 == 0]
        if len(ev) != 1 or nx.node_connectivity(J) < 3:
            continue
        g = Graph(J); z = g.lab[ev[0]]
        c['graphs'] += 1
        c['lovasz_all'] += bool(search(g, lovasz_prof(g)))
        N = [w for (w, e) in g.adj[z]]
        for u in N:
            c['EEn'] += 1
            c['EE'] += short_at(g, z, u, False)
            c['STS'] += short_at(g, z, u, True)
        for S in itertools.combinations(N, len(N) // 2):
            c['HALFn'] += 1
            c['HALF'] += half(g, z, set(S))
        for M in perfect_matchings(N):
            c['PAIRn'] += 1
            ok = pairing(g, z, set(M))
            c['PAIR'] += ok
            if not ok:
                pairfails.append((l.decode(), [tuple(sorted(p)) for p in M]))
    print(n, json.dumps(c), 'PAIR failures:', pairfails)

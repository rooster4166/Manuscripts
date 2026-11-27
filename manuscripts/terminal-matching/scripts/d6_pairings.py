"""Read g6(G') lines (G' = J - z, even vertices = N(z)); print 'g6 a1 b1 a2 b2 a3 b3' for every
perfect matching of the even vertices.  argv[1] = 'simple': only matchings whose pairs are
non-adjacent in G' (F simple)."""
import sys
import networkx as nx
simple = len(sys.argv) > 1 and sys.argv[1] == 'simple'


def pairings(xs):
    if not xs:
        yield []
        return
    a = xs[0]
    for i in range(1, len(xs)):
        rest = xs[1:i] + xs[i + 1:]
        for p in pairings(rest):
            yield [(a, xs[i])] + p


for line in sys.stdin:
    s = line.strip()
    if not s:
        continue
    G = nx.from_graph6_bytes(s.encode())
    ev = sorted(v for v in G if G.degree(v) % 2 == 0)
    for p in pairings(ev):
        if simple and any(G.has_edge(u, v) for u, v in p):
            continue
        print(s, ' '.join(f'{u} {v}' for u, v in p))

"""A20: STL-P (every pairing) on wheels W_{2k}, own enumerator."""
import sys, time
import networkx as nx
from pdec import Graph, pairing, perfect_matchings, stl
for k in map(int, sys.argv[1:]):
    J = nx.wheel_graph(2 * k + 1)
    g = Graph(J)
    t0 = time.time()
    N = list(range(1, 2 * k + 1))
    tot = ok = 0
    bad = []
    for M in perfect_matchings(N):
        tot += 1
        r = pairing(g, 0, set(M))
        ok += r
        if not r:
            bad.append([tuple(sorted(p)) for p in M])
    print('W%d' % (2 * k), 'pairings', tot, 'realisable', ok, 'failures', bad[:5], 'STL(r=1)', stl(g, 0, 1), '%.1fs' % (time.time() - t0), flush=True)

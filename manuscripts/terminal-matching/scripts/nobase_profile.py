"""Profile of the NOBASE instances of walk.c (E24(F)): distance between the two edges, whether an
admissible walk exists, density.  usage: nobase_profile.py out/pairs_8.txt out/walk_8_0.txt"""
import sys, collections, statistics
import networkx as nx


def dist_edges(G, e, f):
    return min(nx.shortest_path_length(G, u, w) for u in e for w in f if nx.has_path(G, u, w))


nob = {}
for line in open(sys.argv[2]):
    t = line.split()
    if t and t[0] == 'NOBASE':
        nob[(t[1], tuple(t[2:6]))] = t[6]
tot, bad, m_ok, m_bad = collections.Counter(), collections.Counter(), [], []
for line in open(sys.argv[1]):
    t = line.split()
    G = nx.from_graph6_bytes(t[0].encode())          # G' = G - F
    a, b, c, d = map(int, t[1:5])
    dd = dist_edges(G, (a, b), (c, d))
    key = (t[0], tuple(t[1:5]))
    tot[dd] += 1
    if key in nob:
        bad[(dd, nob[key])] += 1; m_bad.append(G.number_of_edges())
    else:
        m_ok.append(G.number_of_edges())
print('instances by distance between the edges:', dict(sorted(tot.items())))
print('NOBASE by (distance, admissible walk exists):', dict(sorted(bad.items())))
print(f'mean |E(G-F)|: base ok {statistics.mean(m_ok):.2f}, NOBASE {statistics.mean(m_bad):.2f}')

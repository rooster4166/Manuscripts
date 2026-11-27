"""NOBASE instances of walk.c by the number of edges of G - F joining the two edges of F
(E24(F)).  usage: connector_profile.py out/pairs_N.txt out/walk_N_0.txt"""
import sys, collections
import networkx as nx

nob = {}
for line in open(sys.argv[2]):
    t = line.split()
    if t and t[0] == 'NOBASE':
        nob[(t[1], tuple(t[2:6]))] = t[6]
tot, bad = collections.Counter(), collections.Counter()
for line in open(sys.argv[1]):
    t = line.split()
    G = nx.from_graph6_bytes(t[0].encode())
    a, b, x, y = map(int, t[1:5])
    c = sum(G.has_edge(u, v) for u in (a, b) for v in (x, y))
    tot[c] += 1
    key = (t[0], tuple(t[1:5]))
    if key in nob:
        bad[(c, nob[key])] += 1
for c in sorted(tot):
    print(f'connectors={c} instances={tot[c]} NOBASE_with_walk={bad[(c, "anypath=1")]} '
          f'no_admissible_walk={bad[(c, "anypath=0")]}')

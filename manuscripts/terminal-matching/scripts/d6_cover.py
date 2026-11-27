"""Per J: which r in N(z) are long ends of some simple pairing whose chained-walk base exists.
usage: d6_cover.py G6FILE WALK3_ALL_OUTPUT   (G6FILE: the g6(J - z) lines)"""
import sys, collections
import networkx as nx
Js = [l.strip() for l in open(sys.argv[1]) if l.strip()]
cov = collections.defaultdict(set)
for line in open(sys.argv[2]):
    if line.startswith('BASE'):
        t = line.split(); F = list(map(int, t[2:8])); sh = set(map(int, t[9:12]))
        cov[t[1]] |= set(F) - sh
full = part = none = nosimple = 0
hist = collections.Counter()
simple_any = collections.Counter()
for g in Js:
    G = nx.from_graph6_bytes(g.encode())
    N = {v for v in G if G.degree(v) % 2 == 0}
    c = len(cov[g] & N)
    hist[c] += 1
print('J', len(Js), 'covered r per J (histogram 0..6):', dict(sorted(hist.items())))

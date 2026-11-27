"""Compare the least k of a hubroot log of hs_test.py with the parity lower bound.
Usage: python3 hs_parity.py FILE.g6 LOG
With F = star(y) + X the seed is Lovász's, so G - F may have at most one even vertex of positive
degree. In G - star(y) the even vertices of positive degree other than y are the odd neighbours
of y that are not leaves and the even vertices outside N[y]; call their number e(y). An edge of
X changes the parity of its two ends (or isolates a vertex), so |X| >= lb(y) = floor(e(y) / 2).
Prints the tally
of (lb, k) over all root orbits, where k is the least number of extra edges (0 when the log has
no line for the root)."""
import sys, os
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from hs_test import roots_bb3

path, log = sys.argv[1], sys.argv[2]
kof = {}
for line in open(log):
    if line.startswith("TALLY"):
        continue
    w = line.split()
    kof[(w[0], int(w[2]))] = w[3]
tally = Counter()
for g6 in (l.strip() for l in open(path) if l.strip()):
    G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(g6.encode()))
    d = dict(G.degree())
    for y in roots_bb3(G):
        # leaves at y become isolated in G - star(y) and do not count
        e = sum(1 for v in G if v != y and ((v in G[y] and d[v] % 2 == 1 and d[v] > 1) or
                                           (v not in G[y] and d[v] % 2 == 0)))
        lb = e // 2
        k = kof.get((g6, y), "k=0")
        tally[(lb, k)] += 1
        if int(k[2]) > lb + 1:
            print("EXCESS", g6, "root", y, "lb", lb, k, flush=True)
for (lb, k), c in sorted(tally.items()):
    print(f"lb={lb} {k}: {c}")
print("total", sum(tally.values()))

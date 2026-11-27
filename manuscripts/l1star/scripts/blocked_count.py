"""Counts of L1* instances (1 <= |A| <= K, A admissible, A of positive-degree vertices) in graphs
with exactly one even vertex, by the reduction of Theorem 4.2 used in the proof of Theorem 4.3
(l1star session).  Priority: (a) c in N(g); then (c) a free u in N(c); then (b) a free u not in N(c);
otherwise blocked.
usage: nauty-geng -cq n | python3 blocked_count.py K
"""
import sys, itertools, collections
import networkx as nx
K = int(sys.argv[1])
C = collections.Counter()
for line in sys.stdin:
    G = nx.from_graph6_bytes(line.strip().encode())
    ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    if len(ev) != 1: continue
    g = ev[0]; Ng = set(G[g])
    for c in G:
        if G.degree(c) % 2 == 0: continue
        bad = set(G[c]) | {c} | Ng
        cand = [v for v in G if v not in bad and G.degree(v) > 0]
        for k in range(1, K + 1):
            for S in itertools.combinations(cand, k):
                A = set(S)
                C["instances"] += 1
                if c in Ng: C["(1) c in N(g)"] += 1; continue
                free = [x for x in Ng if not ((set(G[x]) & A) - {g})]
                if any(x in G[c] for x in free): C["(3) free u in N(c)"] += 1; continue
                if free: C["(2) free u not in N(c)"] += 1; continue
                C["BLOCKED" + (" g in A" if g in A else " g not in A")] += 1
for k, v in sorted(C.items()): print(k, v)

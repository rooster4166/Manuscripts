"""Classify the L1* instances (|A| <= K) to which none of the moves M1, M2, M9 applies.
(l1star session, exploratory; see moves.py for the moves)
usage: nauty-geng -cq n | python3 irred.py K
"""
import sys, itertools, collections
import networkx as nx
K = int(sys.argv[1])
C = collections.Counter(); ex = collections.defaultdict(list)
for line in sys.stdin:
    line = line.strip()
    G = nx.from_graph6_bytes(line.encode())
    ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    if len(ev) != 1: continue
    g = ev[0]; Ng = set(G[g])
    for c in G:
        if G.degree(c) % 2 == 0 or c in Ng: continue
        Nc = set(G[c]) | {c}
        cand = [v for v in G if v not in Nc and v not in Ng]
        for k in range(1, K + 1):
            for S in itertools.combinations(cand, k):
                A = set(S)
                C["total"] += 1
                if any(not ((set(G[u]) & A) - {g}) for u in Ng): continue
                if g not in A and nx.has_path(G.subgraph(set(G) - A), g, c): continue
                H = G.subgraph((set(G) - A - Nc - {g}) | {g})
                reach = nx.node_connected_component(H, g) - {g}
                if any(not (set(G[z]) & A) for z in reach): continue
                typ = ("gA" if g in A else "sep") + f" |A|={k} d(g)={G.degree(g)} d(c)={G.degree(c)}"
                C[typ] += 1
                if len(ex[typ]) < 2: ex[typ].append((line, g, c, sorted(A)))
for k, v in sorted(C.items()): print(k, v, ex.get(k, ""))

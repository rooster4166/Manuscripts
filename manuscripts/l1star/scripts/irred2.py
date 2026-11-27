"""Irreducible L1* instances under the extended move set (l1star session, exploratory).
Moves:
  M1  : u in N(g) with N(u) & A <= {g}
  M2  : g not in A, g and c connected in G - A
  M2' : a route g ... y c (y in N(c)) with interior outside A, N[y] & A empty, interior other
        than y outside N(c)
  M9* : a route g e1 ... ek (k >= 1), c not on it, ei outside A, ek with N(ek) & A <= {g},
        every ei outside N(c) unless d(c) = 1
usage: nauty-geng -cq n | python3 irred2.py K
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
        Nc = set(G[c]); NNc = Nc | {c}
        cand = [v for v in G if v not in NNc and v not in Ng]
        for k in range(1, K + 1):
            for S in itertools.combinations(cand, k):
                A = set(S)
                C["total"] += 1
                if any(not ((set(G[u]) & A) - {g}) for u in Ng): continue
                if g not in A and nx.has_path(G.subgraph(set(G) - A), g, c): continue
                # M9*: allowed route vertices
                allowed = set(G) - A - {c, g}
                if G.degree(c) != 1: allowed -= Nc
                H = G.subgraph(allowed | {g})
                reach = nx.node_connected_component(H, g) - {g}
                if any(not (set(G[z]) & A) for z in reach): continue
                # M2': y in N(c), N[y] & A empty, route g..y with interior outside A and N(c)
                ok = False
                for y in Nc:
                    if (set(G[y]) | {y}) & A: continue
                    if y == g: ok = True; break
                    H2 = G.subgraph((set(G) - A - NNc) | {g, y})
                    if nx.has_path(H2, g, y): ok = True; break
                if ok: continue
                typ = ("gA" if g in A else "sep") + f" |A|={k} d(g)={G.degree(g)} d(c)={G.degree(c)}"
                C[typ] += 1
                if len(ex[typ]) < 2: ex[typ].append((line, g, c, sorted(A)))
for k, v in sorted(C.items()): print(k, v, ex.get(k, ""))

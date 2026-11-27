"""L1* instances (|A| <= K) to which none of the reductions of the manuscript applies, one level
deep (l1star session).  Reductions: M1 (Case I at g, Theorem 4.2 (b), (c)); shrink A to the
boundary of the component of c in G - A (Lemma 5.1); M2 (route g..c appended, g not in A; Proposition 5.2);
M9 (Fan route from g to a vertex with no neighbour in A; Proposition 5.3); M7 (d(g) = 2,
N(g) = {u, v} non-adjacent: split off g; Proposition 5.4(i)); M13 (d(g) = 2, uv an edge, g in A:
drop g from A; Proposition 5.4(ii)); M8 (d(c) = 3, split off two non-adjacent neighbours one of
which is not in N(g); Proposition 5.5).
Counts: instances with 1 <= |A| <= 2 and c not in N(g) (the c in N(g) instances are reducible by
Theorem 4.2(a) and are not listed).
usage: nauty-geng -cq n | python3 irred_all.py K
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
                comp = nx.node_connected_component(G.subgraph(set(G) - A), c)
                bd = {a for a in A if set(G[a]) & comp}
                if bd != A:
                    C["shrink"] += 1; continue          # a smaller counterexample would exist
                if any(not ((set(G[u]) & A) - {g}) for u in Ng):
                    C["M1"] += 1; continue
                if g not in A and g in comp:
                    C["M2"] += 1; continue
                allowed = set(G) - A - {c, g}
                if G.degree(c) != 1: allowed -= Nc
                H = G.subgraph(allowed | {g})
                if any(not (set(G[z]) & A) for z in nx.node_connected_component(H, g) - {g}):
                    C["M9"] += 1; continue
                if G.degree(g) == 2:
                    u, v = sorted(Ng)
                    if G.has_edge(u, v):
                        if g in A: C["M13"] += 1; continue
                    else:
                        if g not in A or u not in Nc or v not in Nc:
                            C["M7"] += 1; continue
                if G.degree(c) == 3:
                    done = False
                    for y1, y2 in itertools.permutations(sorted(Nc), 2):
                        if not G.has_edge(y1, y2) and y1 not in Ng:
                            done = True; break
                    if done: C["M8"] += 1; continue
                typ = ("gA" if g in A else "sep") + f" |A|={k} d(g)={G.degree(g)} d(c)={G.degree(c)}"
                C["RESIDUAL " + typ] += 1
                if len(ex[typ]) < 3: ex[typ].append((line, g, c, sorted(A)))
for k, v in sorted(C.items()): print(k, v)
for k, v in ex.items(): print("EX", k, v)

"""girth5proof.py N: test the case analysis of the proof of Theorem 6.1 on every connected all-odd graph
of girth >= 5 and order N (nauty-geng -ctf), every pair of disjoint edges ab, cd and both prescribed
ends: take every shortest walk P between {a,b} and {c,d}, orient as in the proof (u = a: y = w;
u = b: swap the roles of the edges and reverse P), and check (i) admissibility of P,
(ii) the sparse hypotheses of Theorem 5.2 for the resulting base graph."""
import sys, itertools, subprocess
import networkx as nx
from bf import parse_g6
from walkcheck_lib import base_graph, sparse_hyp
N = int(sys.argv[1])
g6s = subprocess.run(['nauty-geng', '-ctfq', str(N)], capture_output=True, text=True).stdout.split()
cnt = dict(cases=0, inadmissible=0, notsparse=0)
for s in g6s:
    n, A = parse_g6(s)
    if any(sum(r) % 2 == 0 for r in A): continue
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from((u, v) for u in range(n) for v in range(u + 1, n) if A[u][v])
    E = list(G.edges())
    for e1, e2 in itertools.permutations(E, 2):
        if set(e1) & set(e2): continue
        for a, b in (e1, e1[::-1]):          # ab with prescribed short end a
            c, d = e2
            k = min(nx.shortest_path_length(G, w, u) for u in (a, b) for w in (c, d))
            for u in (a, b):
                for w in (c, d):
                    if nx.shortest_path_length(G, w, u) != k: continue
                    for P in nx.all_shortest_paths(G, w, u):
                        if u == a:
                            A_, B_, Y_ = a, b, w; X_ = d if w == c else c; PP = P
                        else:
                            A_, B_ = w, (d if w == c else c); X_, Y_ = a, b; PP = P[::-1]
                        cnt['cases'] += 1
                        ok = B_ not in PP and X_ not in PP and all(not A[p][X_] for p in PP[1:-1])
                        if not ok:
                            cnt['inadmissible'] += 1; print('INADMISSIBLE', s, A_, B_, X_, Y_, PP); continue
                        Bm = base_graph(n, A, A_, B_, X_, Y_, PP)
                        if not sparse_hyp(Bm, (X_, Y_, A_, n)):
                            cnt['notsparse'] += 1; print('NOT SPARSE', s, A_, B_, X_, Y_, PP)
print('N=%d' % N, cnt)

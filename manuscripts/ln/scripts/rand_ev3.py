"""random graphs whose even vertices are pairwise at distance >= 3 (>= 2 even vertices):
start from a random graph, then repair parity by adding pendant leaves, keeping chosen even vertices."""
import sys, random
from lnlib import g6_encode
rng = random.Random(int(sys.argv[1])); cnt = int(sys.argv[2]); nmin, nmax = int(sys.argv[3]), int(sys.argv[4])
out = 0
while out < cnt:
    n = rng.randint(nmin, nmax)
    p = rng.uniform(0.2, 0.7)
    adj = [set() for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            if rng.random() < p: adj[i].add(j); adj[j].add(i)
    # choose a set Z of vertices pairwise at distance >= 3, to be the even vertices
    order = list(range(n)); rng.shuffle(order)
    Z = []
    for v in order:
        if all(v not in adj[z] and not (adj[v] & adj[z]) for z in Z) and adj[v]:
            Z.append(v)
        if len(Z) >= rng.randint(2, 4): break
    if len(Z) < 2: continue
    # fix parities: vertices outside Z must be odd: toggle edges to new leaves; Z must be even:
    # a vertex in Z with odd degree: remove an edge to a non-Z vertex? simpler: skip
    if any(len(adj[z]) % 2 for z in Z): continue
    N = n
    for v in range(n):
        if v in Z: continue
        if len(adj[v]) % 2 == 0:
            adj.append({v}); adj[v].add(N); N += 1
    if N > 22: continue
    # check distance condition still holds (new leaves attached to non-Z vertices may create common nbrs? no: leaf adj to one vertex)
    print(g6_encode(N, adj)); out += 1

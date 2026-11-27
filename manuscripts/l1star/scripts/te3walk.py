"""TE3 (two even vertices at distance >= 3): do 'pair walks' reduce every instance?
A step moves one even vertex x to a neighbour u (delete xu); it is a legal Fan step if the other
even vertex is not adjacent to u in the current graph.  A walk certifies TE3 if it ends with an
even vertex of degree 0 or with the pair at distance >= 3 (and at least one step: induction).
usage: nauty-geng -cq n | python3 te3walk.py MAXSTEPS
"""
import sys, collections
import networkx as nx
MAX = int(sys.argv[1])

def far(G, a, b):
    return not G.has_edge(a, b) and not (set(G[a]) & set(G[b]))

def walk(G, x, y, steps):
    if G.degree(x) == 0 or G.degree(y) == 0:
        return True
    if steps > 0 and far(G, x, y):
        return True
    if steps >= MAX:
        return False
    for (p, q) in ((x, y), (y, x)):
        for u in list(G[p]):
            if u == q or G.has_edge(u, q):
                continue
            H = G.copy(); H.remove_edge(p, u)
            if walk(H, u, q, steps + 1):
                return True
    return False

C = collections.Counter(); ex = []
for line in sys.stdin:
    G = nx.from_graph6_bytes(line.strip().encode())
    ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    if len(ev) != 2: continue
    x, y = ev
    if not far(G, x, y): continue
    ok = walk(G, x, y, 0)
    C[ok] += 1
    if not ok and len(ex) < 5: ex.append(line.strip())
print(dict(C), ex)

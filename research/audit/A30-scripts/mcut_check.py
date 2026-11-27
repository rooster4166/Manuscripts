"""A30 audit: independent matching-cut count (brute force over bipartitions) for the
2-connected Eulerian graphs of even order; compare with the manuscript's 0, 5, 130, 27,933."""
import sys
import networkx as nx

def has_mc(B):
    n = B.number_of_nodes()
    nb = [0]*n
    for u, v in B.edges(): nb[u] |= 1 << v; nb[v] |= 1 << u
    full = (1 << n) - 1
    for X in range(1, 1 << (n-1)):   # vertex n-1 always outside X: each cut once
        ok = True
        for v in range(n):
            across = nb[v] & (full ^ X) if (X >> v) & 1 else nb[v] & X
            if across & (across - 1): ok = False; break
        if ok: return True
    return False

for fn in sys.argv[1:]:
    tot = no = 0
    for l in open(fn):
        B = nx.from_graph6_bytes(l.strip().encode()); tot += 1
        if not has_mc(B): no += 1
    print(fn, 'graphs', tot, 'without matching cut', no)

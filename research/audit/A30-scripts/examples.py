"""A30 audit: checks of Example 4.2, the five 'full CB' roots, GCXnbW, K_{2,10}, and the
m = 45 gap in the order-12 dense family claim (Section 6.3)."""
import math, itertools, random
import networkx as nx

def CB(B, r):
    degs = [d for _, d in B.degree()]; dr = B.degree(r); p = 1
    while True:
        c = [min(d, 2*p-d) for d in degs]
        if min(dr, 2*p-dr) >= 2 and min(c) >= 0 and sum(c) >= 2*p: return p
        p += 1
def classical(B, r):
    n, m = B.number_of_nodes(), B.number_of_edges()
    return max(B.degree(r)//2 + 1, math.ceil(max(d for _, d in B.degree())/2), math.ceil(m/(n-1)))

# Example 4.2
B = nx.from_graph6_bytes(b'GTm~vs')
Bc = nx.complement(B)
print('GTm~vs: n,m', B.number_of_nodes(), B.number_of_edges(), 'degrees', sorted(d for _, d in B.degree()),
      'biconnected', nx.is_biconnected(B))
print('  complement edges', sorted(Bc.edges()), 'complement degrees', dict(Bc.degree()))
print('  CB per root', [CB(B, r) for r in B], 'classical per root', [classical(B, r) for r in B])

for g6, roots in [('IEl}}~^vw', [0, 1, 2]), ('ITm||~}~g', [1, 7]), ('I]zn^^nzw', [0, 1]), ('ITzvn^nzw', [4])]:
    B = nx.from_graph6_bytes(g6.encode())
    print(g6, 'm', B.number_of_edges(), [(r, B.degree(r), CB(B, r), classical(B, r)) for r in roots])

# GCXnbW
B = nx.from_graph6_bytes(b'GCXnbW')
print('GCXnbW degrees', dict(B.degree()), 'cut vertices', list(nx.articulation_points(B)),
      'blocks', [sorted(c) for c in nx.biconnected_components(B)], 'CB(6)', CB(B, 6))

# K_{2,10}
K = nx.complete_bipartite_graph(2, 10)
print('K2,10 CB at the two big roots', CB(K, 0), CB(K, 1), 'n/2', 6)

# order 12 with m = 45: complement has 21 edges, all degrees odd. Find one with B 2-connected.
random.seed(1)
found = None
for trial in range(20000):
    # random graph on 12 vertices, 21 edges, then check parity
    H = nx.gnm_random_graph(12, 21, seed=random.randrange(10**9))
    if all(d % 2 == 1 for _, d in H.degree()):
        Bm = nx.complement(H)
        if nx.is_biconnected(Bm) and all(d % 2 == 0 for _, d in Bm.degree()):
            found = Bm; break
if found is not None:
    m = found.number_of_edges()
    print('order-12 2-connected Eulerian graph with m =', m, 'ceil(m/11) =', math.ceil(m/11),
          'g6', nx.to_graph6_bytes(found, header=False).decode().strip())
else:
    print('no m=45 example found by random search')

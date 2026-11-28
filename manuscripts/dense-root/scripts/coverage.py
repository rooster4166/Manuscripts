"""coverage.py: per data set, the roots of degree n-2 covered by
  A   = Theorem A (B - r has <= 1 even vertex; condition (**_eps)),
  B0  = Theorem B with a connector of length <= 2 whose interior is s (delta = 0),
  B1  = Theorem B with all admissible connectors (lengths 1-3: interior s and at most one neighbour
        y of r, delta <= 1),
  MR  = hypotheses of marked-reduction Thm 47 (>= k-1 universal vertices of B), Thm 74
        (complement of B of max degree <= 2) and Thm 166 (k vertices of degree >= 2k-2 in B containing
        r, with u universal ones and the end budget sum b_y = u feasible), Thm 50 (k - c universal,
        1 <= c <= 2k/15, |E(B[X])| <= k^2/8).
usage: coverage.py LABEL FILE [resid]   (resid: lines are B with N(z) = {0..5})"""
import sys, itertools, networkx as nx
from collections import Counter
sys.path.insert(0, '.')
src = open('thm_cov.py').read()
exec(src.split("C = Counter()")[0])
exec("\n".join(src.split("# ---- extended")[1].split("C2 = Counter()")[0].split("\n")[1:]))
def mr50(B, k):
    U = [v for v in B if B.degree(v) == 2 * k - 1]
    for c in range(1, int(2 * k / 15) + 1):
        if len(U) >= k - c:
            for R in itertools.combinations(U, k - c):
                X = [v for v in B if v not in R]
                if B.subgraph(X).number_of_edges() <= k * k / 8: return True
    return False
label, fn = sys.argv[1], sys.argv[2]
resid = len(sys.argv) > 3
C = Counter(); rows = []
for line in open(fn):
    g6 = line.split()[0]
    if resid:
        B = nx.from_graph6_bytes(g6.encode()); nB = B.number_of_nodes()
        J = B.copy(); J.add_node(nB); [J.add_edge(nB, u) for u in range(6)]
    else:
        J = nx.from_graph6_bytes(g6.encode())
    n = J.number_of_nodes(); k = (n - 1) // 2
    z = [v for v in J if J.degree(v) % 2 == 0][0]
    Z = set(J[z]); B = J.copy(); B.remove_node(z)
    for r in sorted(Z):
        if J.degree(r) != n - 2: continue
        s = [v for v in B if v != r and not B.has_edge(r, v)][0]
        a = thmA(B, r, s, k) is True
        b0 = thmB(B, r, s, k, Z) is True
        b1 = thmB2(B, r, s, k, Z) is True
        m47, m74, m166, m50 = mr47(B, k), mr74(B, k), mr166(B, r, k, Z), mr50(B, k)
        C['roots'] += 1
        C['s in N(z)'] += s in Z
        for key, val in (('A', a), ('B0', b0), ('B1', b1), ('A|B0', a or b0), ('A|B1', a or b1),
                         ('MR47', m47), ('MR74', m74), ('MR166', m166), ('MR50', m50),
                         ('MR any', m47 or m74 or m166 or m50),
                         ('A|B1|MR', a or b1 or m47 or m74 or m166 or m50)):
            C[key] += val
print(label, dict(C))

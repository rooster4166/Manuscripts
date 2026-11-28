"""look.py: the order-9 roots of degree n-2 outside Theorems A and B, by kind
(noQ: s in N(z) and no admissible connector, lengths 1-3; cond: the degree condition fails) and by the number
of neighbours of r in B of degree 7 in J.  Run from scripts/."""
import networkx as nx
from collections import Counter
src = open('thm_cov.py').read()
exec(src.split("C = Counter()")[0])
exec("\n".join(src.split("# ---- extended")[1].split("C2 = Counter()")[0].split("\n")[1:]))
C = Counter()
for line in open('../../multi-token/data/J9_d6.g6'):
    g6 = line.split()[0]
    J = nx.from_graph6_bytes(g6.encode()); n = J.number_of_nodes(); k = (n - 1) // 2
    z = [v for v in J if J.degree(v) % 2 == 0][0]; Z = set(J[z]); B = J.copy(); B.remove_node(z)
    for r in sorted(Z):
        if J.degree(r) != n - 2: continue
        s = [v for v in B if v != r and not B.has_edge(r, v)][0]
        a = thmA(B, r, s, k); b = thmB2(B, r, s, k, Z)
        if a is True or b is True: continue
        N = [x for x in B if x not in (r, s)]
        h7 = sum(1 for x in N if J.degree(x) == 7)
        C[('sinZ' if s in Z else 'snotZ', 'noQ' if b == 'noQ' else 'cond', '#N deg7=%d' % h7)] += 1
for k_, v in sorted(C.items()): print(k_, v)

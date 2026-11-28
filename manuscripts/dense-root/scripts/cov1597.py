# coverage on the unscheduled degree-(n-2) roots of multi-token (data/runs/J9_none.txt)
import networkx as nx
from collections import Counter
src = open('thm_cov.py').read()
exec(src.split("C = Counter()")[0])
exec("\n".join(src.split("# ---- extended")[1].split("C2 = Counter()")[0].split("\n")[1:]))
C = Counter()
for line in open('../../multi-token/data/runs/J9_none.txt'):
    f = line.split(); g6 = f[0]; roots = [int(x) for x in f[1].split(',')]
    J = nx.from_graph6_bytes(g6.encode()); n = J.number_of_nodes(); k = (n - 1) // 2
    z = [v for v in J if J.degree(v) % 2 == 0][0]; Z = set(J[z]); B = J.copy(); B.remove_node(z)
    for r in roots:
        if J.degree(r) != n - 2: continue
        s = [v for v in B if v != r and not B.has_edge(r, v)][0]
        a = thmA(B, r, s, k) is True; b = thmB2(B, r, s, k, Z) is True
        mr = mr47(B, k) or mr74(B, k) or mr166(B, r, k, Z)
        C['roots'] += 1; C['A'] += a; C['B'] += b; C['A|B'] += a or b; C['MR'] += mr; C['all'] += a or b or mr
print(dict(C))

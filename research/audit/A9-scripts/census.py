"""Independent census of connected graphs with exactly two even vertices (orders 4, 6, 8):
tightness (partition into |Od|/2 paths) and the obstruction classes of Prop. 47."""
import sys
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from pathnum2 import decompose
def tight(H):
    odd = [v for v in H if H.degree(v) % 2]
    ex = {v: (1 if H.degree(v) % 2 else 0) for v in H}
    st, P = decompose(H, len(odd) // 2, exact_ends=ex, time_limit=120, workers=1)
    assert P is not None or st == 'INFEASIBLE', st
    return P is not None
def classes(H):
    n = H.number_of_nodes()
    ev = [v for v in H if H.degree(v) % 2 == 0]; u, v = ev
    c = []
    if any(H.degree(w) == n - 1 for w in H if H.degree(w) % 2): c.append('O1')
    if H.has_edge(u, v) and H.degree(u) == H.degree(v) == 2 and set(H[u]) & set(H[v]): c.append('O2')
    if not H.has_edge(u, v) and set(H[u]) == set(H[v]) and len(H[u]) == 2:
        x, y = sorted(H[u])
        if H.has_edge(x, y) and (H.degree(y) == 3 or H.degree(x) == 3): c.append('O3')
    return c
for n in (4, 6, 8):
    tot = nt = 0; cl = {}; twoconn_other = 0
    for line in open(f'/home/user/Manuscripts/data/conn{n}.g6'):
        H = nx.from_graph6_bytes(line.strip().encode())
        if sum(1 for w in H if H.degree(w) % 2 == 0) != 2: continue
        tot += 1
        if tight(H): continue
        nt += 1
        c = classes(H); key = c[0] if c else ('cut' if not nx.is_biconnected(H) else 'other-2conn')
        cl[key] = cl.get(key, 0) + 1
        if not c and nx.is_biconnected(H): twoconn_other += 1
    print(f"n={n}: two-even graphs {tot}, not tight {nt}, first class {cl}, 2-connected non-tight not (O1)-(O3): {twoconn_other}", flush=True)

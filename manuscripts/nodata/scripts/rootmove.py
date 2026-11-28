"""rootmove.py: the root move (MR Thm 145's one-edge step, iterated) at roots without matching data.

For a (T1) instance (J, z, r) with T = N(z) and B = J - z: a path P = r w1 ... wk in B with every
wi outside T, and with r, w1, ..., w_{k-1} each having at most one neighbour in T - r, gives
  (T1) at (J_P, z, wk)  ==>  (T1) at (J, z, r),     J_P = J - E(P) - zr + z wk
(restore the path edges back towards r one at a time with Fan's single-edge lemma; the current
root has >= 2 ends and the restored vertex has at most one neighbour that can have no end).
J_P has the unique even vertex z and N(z) = T - r + wk.  If J[T - r + wk] has a perfect matching,
J_P has matching data, so L_N gives (T1) there by the all-odd matching lift.
Reports, per no-data instance, whether a root move reaches matching data (and the least k).
usage: python3 rootmove.py < ND lines
"""
import sys
from collections import Counter, deque
import networkx as nx


def has_pm(J, S):
    H = J.subgraph(S)
    return 2 * len(nx.max_weight_matching(H, maxcardinality=True)) == len(S)


st = Counter()
for line in sys.stdin:
    if not line.startswith("ND "):
        continue
    g6 = line.split()[1]
    f = line[3 + len(g6):].split("|")[0].split()
    z, r, level = int(f[0]), int(f[1]), int(f[13])
    J = nx.from_graph6_bytes(g6.encode())
    T = set(J[z])
    B = J.copy(); B.remove_node(z)
    Tr = T - {r}
    ok_vertex = lambda v: len(set(B[v]) & Tr) <= 1
    best = None
    if ok_vertex(r):
        # BFS over paths r = w0, w1, ..., wk (simple, wi outside T); internal vertices must be ok
        q = deque([(r, (r,))])
        while q and best is None:
            v, path = q.popleft()
            for w in B[v]:
                if w in T or w in path:
                    continue
                if has_pm(J, Tr | {w}):
                    best = len(path)
                    break
                if ok_vertex(w) and len(path) < 6:
                    q.append((w, path + (w,)))
    key = "r has >= 2 nbrs in T-r" if not ok_vertex(r) else ("move to data, k=%d" % best if best else "no move to data")
    st[(level, key)] += 1
for k, v in sorted(st.items()):
    print(v, k)
print("TOTAL", sum(st.values()))

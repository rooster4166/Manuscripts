"""rootmove2.py: closure of the two root moves of MR Thm 145 at (T1) roots without matching data.

State: a graph J' (z its unique even vertex) and a root rho in N(z).  T' = N_{J'}(z), B' = J' - z.
  M1  rho has at most one neighbour in T' - rho; w a neighbour of rho outside T':
        J'' = J' - rho w - z rho + z w,  new root w.
  M2  rho has exactly two neighbours u, v in T' - rho:
        J'' = J' - rho u - z rho - z u,  new root v   (N(z) loses rho and u).
In both cases (T1) at the new state implies (T1) at the old one (Fan's single-edge lemma, Lean
`fan_single`: the restored vertex rho has no neighbour without an end, or at most one, while the
other end of the restored edge has at least two).  A state has *matching data* if J'[T'] has a
perfect matching; then L_N gives (T1) there (Lean `test1At_of_matchingOdd`).
usage: python3 rootmove2.py [maxdepth] [-p] < ND lines   (-p: one line per instance:
  RM g6 z r level twinR twinO reached moves)
"""
import sys
from collections import Counter, deque
import networkx as nx

maxdepth = int(sys.argv[1]) if len(sys.argv) > 1 else 6
perline = len(sys.argv) > 2 and sys.argv[2] == "-p"   # print one RM line per instance


def has_pm(G, S):
    H = G.subgraph(S)
    return 2 * len(nx.max_weight_matching(H, maxcardinality=True)) == len(S)


def moves(J, z, rho):
    T = set(J[z])
    Tr = T - {rho}
    nb = set(J[rho]) - {z}
    tn = nb & Tr
    out = []
    if len(tn) <= 1:
        for w in nb - T:
            J2 = J.copy()
            J2.remove_edge(rho, w); J2.remove_edge(z, rho); J2.add_edge(z, w)
            out.append(("M1", J2, w))
    if len(tn) == 2:
        a, b = sorted(tn)
        for u, v in ((a, b), (b, a)):
            J2 = J.copy()
            J2.remove_edge(rho, u); J2.remove_edge(z, rho); J2.remove_edge(z, u)
            out.append(("M2", J2, v))
    return out


st = Counter()
for line in sys.stdin:
    if not line.startswith("ND "):
        continue
    g6 = line.split()[1]
    f = line[3 + len(g6):].split("|")[0].split()
    z, r, level = int(f[0]), int(f[1]), int(f[13])
    J = nx.from_graph6_bytes(g6.encode())
    found = None
    q = deque([(J, r, 0, "")])
    seen = set()
    while q and found is None:
        G, rho, d, hist = q.popleft()
        key = (frozenset(frozenset(e) for e in G.edges()), rho)
        if key in seen:
            continue
        seen.add(key)
        if d > 0 and has_pm(G, set(G[z])):
            found = hist
            break
        if d < maxdepth:
            for name, G2, rho2 in moves(G, z, rho):
                q.append((G2, rho2, d + 1, hist + name))
    st[(level, "data via " + found if found else "no data reachable")] += 1
    if perline:
        print("RM", g6, z, r, level, int(f[10]), int(f[11]), "1" if found else "0", found or "-", flush=True)
agg = Counter()
for (lev, k), v in st.items():
    agg[(lev, "reached" if k.startswith("data") else "not")] += v
for k, v in sorted(st.items()):
    print(v, k)
print("BY LEVEL", sorted(agg.items()))
print("TOTAL", sum(st.values()), "reached", sum(v for (l, k), v in agg.items() if k == "reached"))

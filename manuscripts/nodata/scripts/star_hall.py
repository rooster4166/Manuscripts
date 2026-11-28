"""star_hall.py: test the star Hall condition (H1) against the outcomes of nd -UU (nodata session).

(H1) For a vertex u with children X (|X| >= 2) in the rooted forest and every component C of H - u:
     |X cap C| <= (|C| - e_H(u, C)) / 2.
It is necessary: the paths Q(x), x in X cap C, avoid u, so they lie inside C, are distinct and have
one end in X each; and C has |C| ends, e_H(u, C) of them on paths through u.
usage: python3 star_hall.py < USUCC/UFAIL lines
"""
import sys
from collections import Counter, defaultdict
import networkx as nx

def h1_violations(H, par):
    ch = defaultdict(list)
    for v, p in par.items():
        ch[p].append(v)
    bad = []
    for u, X in ch.items():
        if len(X) < 2:
            continue
        Hu = H.copy(); Hu.remove_node(u)
        for C in nx.connected_components(Hu):
            k = len(set(X) & C)
            e = sum(1 for c in C if H.has_edge(u, c))
            if 2 * k > len(C) - e:
                bad.append((u, k, len(C), e))
    return bad

st = Counter(); ex = []
for line in sys.stdin:
    tag = line.split()[0]
    g6 = line.split()[1]
    rest = line[len(tag) + 1 + len(g6) + 1:].split()
    z, r = int(rest[0]), int(rest[1])
    tier = int(rest[3])
    exc = int(rest[5]) if rest[4] == "exc" else -1
    par = [int(x) for x in rest[rest.index("par") + 1:]]
    J = nx.from_graph6_bytes(g6.encode())
    t2 = sum(1 for v in J if J.degree(v) % 2 == 0) == 2
    B = J.copy(); B.remove_node(z)
    Phi = [(v, p) for v, p in enumerate(par) if p >= 0]
    H = B.copy(); H.remove_edges_from(Phi)
    if t2:
        H.add_edge(z, r)
    bad = h1_violations(H, {v: p for v, p in enumerate(par) if p >= 0})
    st[(tier, exc, tag, "H1 violated" if bad else "H1 ok")] += 1
    if tag == "UFAIL" and not bad and len(ex) < 8:
        ex.append((g6, z, r, par))
for k, v in sorted(st.items()):
    print(v, k)
for e in ex:
    print("FAIL-H1ok", *e)

"""A41: check the explicit (T1) decomposition of the theta graph J - h1 (nodata Section 3, after
Theorem 3.3) for t = 2s = 4, 6, ..., 40.  Leaves r, l1, l2, l3 and e1, m1, ..., eq, mq (q = s - 2):
  r h2 l1 h3 l2,  r h3 l3 h2 l2,  h2 h3,  e_i h2 m_i h3 e_{i+1}  (i mod q)    when q != 1;
  for q = 1:  e1 h2 m1 h3  and  e1 h3 h2  replace the last two kinds.
A (T1) decomposition: a partition of E(theta) into paths, at most (|J|-1)/2 = t/2 + 1 of them,
with at least two ends at r.  Also checks the claim that (T1) at h1 needs J 3-connected only for
t >= 4 and that h1 is the unique even vertex for every even t >= 2."""
import itertools
import networkx as nx


def theta(t):
    G = nx.Graph()
    leaves = [f"L{i}" for i in range(t)]
    G.add_edge("h2", "h3")
    for l in leaves:
        G.add_edge(l, "h2")
        G.add_edge(l, "h3")
    return G, leaves


def construction(t):
    s = t // 2
    q = s - 2
    r, l1, l2, l3 = "L0", "L1", "L2", "L3"
    rest = [f"L{i}" for i in range(4, t)]
    e = rest[0::2]
    m = rest[1::2]
    P = [[r, "h2", l1, "h3", l2], [r, "h3", l3, "h2", l2]]
    if q != 1:
        P.append(["h2", "h3"])
        for i in range(q):
            P.append([e[i], "h2", m[i], "h3", e[(i + 1) % q]])
    else:
        P.append([e[0], "h2", m[0], "h3"])
        P.append([e[0], "h3", "h2"])
    return P, r


def check(G, P, r, bound):
    used = set()
    ends = {}
    for path in P:
        assert len(set(path)) == len(path), ("not a path", path)
        for a, b in zip(path, path[1:]):
            assert G.has_edge(a, b), (a, b)
            k = frozenset((a, b))
            assert k not in used
            used.add(k)
        for v in (path[0], path[-1]):
            ends[v] = ends.get(v, 0) + 1
    assert len(used) == G.number_of_edges()
    assert len(P) <= bound, (len(P), bound)
    return ends.get(r, 0)


for t in range(4, 42, 2):
    G, leaves = theta(t)
    P, r = construction(t)
    er = check(G, P, r, t // 2 + 1)
    assert er >= 2
    J = G.copy()
    for l in leaves:
        J.add_edge("h1", l)
    ev = [v for v in J if J.degree(v) % 2 == 0]
    assert ev == ["h1"] or sorted(ev) == ["h1"], ev
    if t <= 12:
        assert nx.node_connectivity(J) == 3
print("explicit construction verified for t = 4, ..., 40 (paths <= t/2 + 1, two ends at r)")
# t = 2: h1 unique even vertex but J not 3-connected
G, leaves = theta(2)
J = G.copy()
for l in leaves:
    J.add_edge("h1", l)
print("t=2: even vertices", [v for v in J if J.degree(v) % 2 == 0], "connectivity", nx.node_connectivity(J))

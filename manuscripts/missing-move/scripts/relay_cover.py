"""How many BranchBase3 root orbits do the proved hub theorems cover?
Usage: python3 relay_cover.py FILE.g6
For each root orbit y (as in hs_test.py) it checks the hypotheses of
  relay: Theorem 6.4 (relay hub): the odd neighbours x_1..x_q of y get distinct even partners
         z_i outside N[y] with x_i z_i an edge; with F = star(y) + {x_i z_i}, G - F - y has at most
         one even vertex w (degree 0 counts as even); no x_i is adjacent to w or to z_j (j != i);
         q >= d(y) - 5.
  twohub: Corollary 6.6 (two hubs): some s2, not adjacent to y, with exactly one common neighbour m,
         2 <= d(y), d(s2) <= 4, and every vertex of G - y - s2 of odd degree.
Prints the tally. With a second argument "check", it also replays both theorems in the game: for
every covered root, the game with path insertion must win with the theorem's own held set. With
"reasons", it prints, for the relay theorem, the first hypothesis that fails at each uncovered
root (the best over all choices of the partners z_i) and the root degrees.
"""
import sys, os
from itertools import permutations
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from hs_test import roots_bb3


def relay_reason(G, y):
    d = dict(G.degree()); N = set(G[y])
    No = sorted(v for v in N if d[v] % 2 == 1)
    if len(No) < d[y] - 5:
        return "(iii) q < d-5"
    cand = [v for v in G if v != y and v not in N and d[v] % 2 == 0]
    best = "no partners z_i (|candidates| < q or no edges x_i z_i)"
    for Z in permutations(cand, len(No)):
        if any(not G.has_edge(x, z) for x, z in zip(No, Z)):
            continue
        H = G.copy(); H.remove_edges_from([(y, v) for v in N]); H.remove_edges_from(zip(No, Z))
        H.remove_node(y)
        ev = [v for v in H if H.degree(v) % 2 == 0]
        if len(ev) > 1:
            if best.startswith("no partners"):
                best = "(i) >= 2 even vertices in G-F-y"
            continue
        bad = set(ev) | set(Z)
        if any(G.has_edge(x, u) for i, x in enumerate(No) for u in bad if u != Z[i]):
            best = "(ii) adjacency"
            continue
        return "covered"
    return best


def relay_ok(G, y):
    return relay_F(G, y) is not None


def relay_F(G, y):
    """The held set star(y) + {x_i z_i} of the relay theorem, or None."""
    d = dict(G.degree()); N = set(G[y])
    No = sorted(v for v in N if d[v] % 2 == 1)
    if len(No) < d[y] - 5:
        return None
    cand = [v for v in G if v != y and v not in N and d[v] % 2 == 0]
    for Z in permutations(cand, len(No)):
        if any(not G.has_edge(x, z) for x, z in zip(No, Z)):
            continue
        H = G.copy(); H.remove_edges_from([(y, v) for v in N]); H.remove_edges_from(zip(No, Z))
        H.remove_node(y)
        ev = [v for v in H if H.degree(v) % 2 == 0]
        if len(ev) > 1:
            continue
        bad = set(ev) | set(Z)
        if any(G.has_edge(x, u) for i, x in enumerate(No) for u in bad if u != Z[i]):
            continue
        return [(y, v) for v in sorted(N)] + list(zip(No, Z))
    return None


def twohub_ok(G, y):
    return twohub_F(G, y) is not None


def twohub_F(G, y):
    """The held set star(y) + star(s2) of the two-hub corollary, or None."""
    d = dict(G.degree())
    if d[y] > 4:
        return None
    for s2 in G:
        if s2 == y or G.has_edge(y, s2) or not 2 <= d[s2] <= 4:
            continue
        if len(set(G[y]) & set(G[s2])) != 1:
            continue
        H = G.copy(); H.remove_nodes_from([y, s2])
        if all(H.degree(v) % 2 == 1 for v in H):
            return [(y, v) for v in G[y]] + [(s2, v) for v in G[s2]]
    return None


tally = Counter()
for g6 in (l.strip() for l in open(sys.argv[1]) if l.strip()):
    G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(g6.encode()))
    for y in roots_bb3(G):
        r, t = relay_ok(G, y), twohub_ok(G, y)
        tally["roots"] += 1
        tally["relay"] += r
        tally["twohub"] += t
        tally["either"] += r or t
print(dict(tally))

if len(sys.argv) > 2 and sys.argv[2] == "reasons":
    t, dd = Counter(), Counter()
    for g6 in (l.strip() for l in open(sys.argv[1]) if l.strip()):
        G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(g6.encode()))
        d = dict(G.degree())
        for y in roots_bb3(G):
            t[relay_reason(G, y)] += 1; dd[d[y]] += 1
    print("relay theorem, first failing hypothesis (best over choices of z):", dict(t))
    print("root degrees:", dict(sorted(dd.items())), "(Corollary 6.6 needs d(y) <= 4)")

if len(sys.argv) > 2 and sys.argv[2] == "check":
    # replay: for every root covered by a theorem, the game with path insertion wins with the
    # theorem's own held set
    import fan_game as fg
    res = Counter()
    for g6 in (l.strip() for l in open(sys.argv[1]) if l.strip()):
        G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(g6.encode()))
        for y in roots_bb3(G):
            for name, F in (("relay", relay_F(G, y)), ("twohub", twohub_F(G, y))):
                if F is None:
                    continue
                r = fg.solve_graph(G, 0, roots=[y], newpath=True, fixedF=F)
                res[name + (" win" if r[y] is not None else " LOSE")] += 1
                if r[y] is None:
                    print("LOSE", name, g6, y, F, flush=True)
    print("replay", dict(res))

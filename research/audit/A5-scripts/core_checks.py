import itertools, networkx as nx
from marked import q_all
from seglib import dihedral, canon_path, canon_cycle
def check(G, name):
    n = G.number_of_nodes()
    res = q_all(G)
    bad = {tuple(sorted(S)): v for S, v in res.items() if v > (n - len(S)) // 2}
    print(f"{name}: n={n} m={G.number_of_edges()} marksets={len(res)} violations={bad}")
    return not bad
# Section 3: K5 and K5-ab
K5 = nx.complete_graph(5); check(K5, "K5")
K5e = nx.complete_graph(5); K5e.remove_edge(0, 1); check(K5e, "K5-ab")
# Section 4: six-cycle + Hamilton path of chords (all labelled), octahedron
C6 = [(i, (i+1) % 6) for i in range(6)]
chords = [e for e in itertools.combinations(range(6), 2) if abs(e[0]-e[1]) not in (1, 5)]
hp = []; hc = []
for p in itertools.permutations(range(6)):
    L = [frozenset((p[i], p[i+1])) for i in range(5)]
    if all(tuple(sorted(l)) in chords for l in L) and p[0] < p[-1]: hp.append(p)
    if p[0] == 0 and p[1] < p[-1] and all(tuple(sorted(l)) in chords for l in L) and tuple(sorted((p[5], p[0]))) in chords: hc.append(p)
D6 = dihedral(6)
print("Hamilton chord paths (labelled):", len(hp), " up to D6 x rev:", len({canon_path(p, D6) for p in hp}))
print("Hamilton chord cycles (labelled):", len(hc), " up to symmetry:", len({canon_cycle(p, D6) for p in hc}))
ok = True
for p in sorted({canon_path(p, D6) for p in hp}):
    G = nx.Graph(C6); G.add_edges_from((p[i], p[i+1]) for i in range(5))
    ok &= check(G, f"C6+path{p}")
for p in sorted({canon_cycle(p, D6) for p in hc}):
    G = nx.Graph(C6); G.add_edges_from((p[i], p[(i+1) % 6]) for i in range(6))
    ok &= check(G, f"C6+cycle{p}")
print("core-only six all OK:", ok)

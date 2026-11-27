"""A11: Proposition 8 (family G_{t,t'}) and the six N = 7, e = 5 failures."""
import networkx as nx
from exact import floor_with_end, check_partition
from counterexamples import as_dict, even_set, le_paths, is_set

def Gtt(t, t2):
    G = nx.Graph([('y', 's'), ('y', "s'")])
    for i in range(t): G.add_edges_from([('s', f'u{i}'), ('s', f'v{i}'), (f'u{i}', f'v{i}')])
    for j in range(t2): G.add_edges_from([("s'", f"u'{j}"), ("s'", f"v'{j}"), (f"u'{j}", f"v'{j}")])
    return G

for t, t2 in [(1, 0), (2, 0), (1, 1), (3, 0), (2, 1), (4, 0), (3, 1), (2, 2)]:
    G = Gtt(t, t2); D = as_dict(G); N = len(D)
    Ev = even_set(G); H = G.subgraph(Ev)
    assert N == 3 + 2 * (t + t2) and nx.is_connected(G)
    assert H.degree('y') == 0 and H.number_of_edges() == t + t2 and len(Ev) == 1 + 2 * (t + t2)
    assert [v for v in G if G.degree(v) % 2] in (['s', "s'"], ["s'", 's']) or set(v for v in G if G.degree(v) % 2) == {'s', "s'"}
    assert floor_with_end(D, 'y') is None
    P = le_paths(D, (N - 1) // 2)
    assert P is not None and check_partition(D, P) and not is_set(G)
    print(f'G_{{{t},{t2}}}: N={N}, e={len(Ev)}: floor holds, no floor partition ends at y')

# the six exact failures at N = 7, e = 5
iso = {}
for G in nx.read_graph6('/home/user/Manuscripts/data/conn7.g6'):
    Ev = even_set(G)
    if len(Ev) != 5 or max(d for _, d in G.subgraph(Ev).degree()) > 3: continue
    D = as_dict(G)
    for y in Ev:
        if floor_with_end(D, y) is None:
            H = G.subgraph(Ev)
            nbr = sorted((w, G.degree(w), w in Ev) for w in G[y])
            print('N=7 e=5 failure:', nx.to_graph6_bytes(G, header=False).strip().decode(), 'd(y)=', G.degree(y),
                  'y-nbrs (vertex, degree, even?)', nbr, '| even subgraph edges', H.number_of_edges(),
                  'degrees', sorted(d for _, d in H.degree()))
            for t, t2 in [(1, 1), (2, 0)]:
                if nx.is_isomorphic(G, Gtt(t, t2)): print('    = G_{%d,%d}' % (t, t2))

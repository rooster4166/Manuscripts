"""A11: Section 3 of bs-prescribed (the prescribed-end statement is false), with exact.py.
Proposition 8 (the family G_{t,t'} of the current draft) is checked in family_tt.py.

1. The family G_t of the first draft (h, y, g and t triangles at h), t = 2, 4: no partition into (N-1)/2 paths with an end at y, but a
   floor partition exists (so the obstruction is the prescription).
2. The order-5 example of the text.
3. Proposition 9: L (order 9) has p(L) = 4 exactly; the doubled gadget D (order 17) has no
   partition into 8 paths with an end at y, while p(D) <= 8.
4. Census (Table 1, exact rows): connected graphs of order 5 and 7 (data/conn5.g6, conn7.g6) whose
   even subgraph has maximum degree <= 3, and even y; count (G, y) with no floor partition ending
   at y, by the number e of even vertices, and how many of the failing G are SET graphs.
"""
import itertools
import sys

import networkx as nx

from exact import realise, check_partition, floor_with_end


def as_dict(Gx):
    return {v: set(Gx[v]) for v in Gx}


def le_paths(G, budget):
    """A partition into <= budget paths, or None (all end vectors between parity and 2*budget)."""
    deg = {v: len(G[v]) for v in G}
    base = {v: deg[v] % 2 for v in G}
    slack = 2 * budget - sum(base.values())
    if slack < 0:
        return None
    verts = [v for v in G if deg[v] > 0]
    for extra in range(0, slack // 2 + 1):
        for combo in itertools.combinations_with_replacement(verts, extra):
            beta = dict(base)
            for w in combo:
                beta[w] += 2
            if any(beta[w] > deg[w] for w in G):
                continue
            P = realise(G, beta)
            if P is not None:
                return P
    return None


def G_t(t):
    Gx = nx.Graph()
    Gx.add_edges_from([('h', 'y'), ('y', 'g')])
    for i in range(t):
        Gx.add_edges_from([('h', f's{i}'), (f's{i}', f'u{i}'), (f's{i}', f'v{i}'), (f'u{i}', f'v{i}')])
    return Gx


def even_set(Gx):
    return [v for v in Gx if Gx.degree(v) % 2 == 0 and Gx.degree(v) > 0]


def is_set(Gx):
    Ev = even_set(Gx)
    if len(Ev) != 3 or Gx.subgraph(Ev).number_of_edges() != 3:
        return False
    return all(sum(1 for w in Gx[v] if w in Ev) >= 2 for v in Gx if v not in Ev)


def part1():
    for t in (2, 4):
        Gx = G_t(t)
        G = as_dict(Gx)
        N = len(G)
        Ev = even_set(Gx)
        H = Gx.subgraph(Ev)
        assert N == 3 * t + 3 and nx.is_connected(Gx)
        assert sorted(map(sorted, H.edges())) == sorted(sorted((f'u{i}', f'v{i}')) for i in range(t))
        assert 'y' in Ev and H.degree('y') == 0 and Gx.degree('h') % 2 == 1 and Gx.degree('g') == 1
        bad = floor_with_end(G, 'y')
        good = le_paths(G, (N - 1) // 2)
        assert bad is None and good is not None and check_partition(G, good)
        print(f'  G_{t}: N={N}, no partition into {(N-1)//2} paths with an end at y; '
              f'p(G_{t}) <= {(N-1)//2} (witness of {len(good)} paths)')


def part2():
    # y on a triangle y p q with p, q of degree two; y has two further leaves r, s
    Gx = nx.Graph([('y', 'p'), ('y', 'q'), ('p', 'q'), ('y', 'r'), ('y', 's')])
    G = as_dict(Gx)
    assert floor_with_end(G, 'y') is None and le_paths(G, 2) is not None
    assert not is_set(Gx)
    print('  order 5 (triangle ypq, leaves r, s at y): floor 2 holds, but no 2-path partition ends at y')


def gadget():
    L = nx.Graph()
    L.add_edges_from([('x', 'a1'), ('x', 'b1'), ('a1', 'b1'), ('x', 'a2'), ('x', 'b2'), ('a2', 'b2'),
                      ('x', 's'), ('x', 'w'), ('s', 'l'), ('s', 'w'), ('w', 'z')])
    return L


def part3():
    L = gadget()
    G = as_dict(L)
    assert len(G) == 9 and nx.is_connected(L)
    Ev = even_set(L)
    assert sorted(Ev) == sorted(['x', 'a1', 'b1', 'a2', 'b2'])
    Hb = L.subgraph(Ev)
    assert Hb.number_of_edges() == 6 and Hb.degree('x') == 4  # bowtie
    assert L.degree('l') == 1 and L.degree('s') % 2 == 1
    P = [('a1', 'b1', 'x', 'b2', 'a2'), ('a1', 'x', 'a2'), ('l', 's', 'x', 'w', 'z'), ('s', 'w')]
    assert check_partition(G, P)
    assert le_paths(G, 3) is None
    odd = [v for v in L if L.degree(v) % 2]
    print(f'  L: printed 4-path partition valid, no 3-path partition, so p(L) = 4 '
          f'(the odd vertices {sorted(odd)} alone only force 2 paths)')
    # D: two copies of L - l, bridge s s', new vertex y adjacent to x, x'
    D = nx.Graph()
    for tag in ('', "'"):
        for a, b in L.edges():
            if 'l' in (a, b):
                continue
            D.add_edge(a + tag, b + tag)
    D.add_edge('s', "s'")
    D.add_edge('y', 'x')
    D.add_edge('y', "x'")
    GD = as_dict(D)
    assert len(GD) == 17
    EvD = even_set(D)
    HD = D.subgraph(EvD)
    assert sorted(EvD) == sorted(['y'] + [v + t for v in ('a1', 'b1', 'a2', 'b2') for t in ('', "'")])
    assert HD.number_of_edges() == 4 and HD.degree('y') == 0 and max(d for _, d in HD.degree()) <= 1
    assert sum(1 for v in D if D.degree(v) % 2) == 8
    assert floor_with_end(GD, 'y', budget=8) is None
    W = le_paths(GD, 8)
    assert W is not None and check_partition(GD, W)
    print('  D: order 17, even subgraph 4K2 + K1, 8 odd vertices; p(D) <= 8 but no 8-path partition ends at y')


def part4():
    for N, f in ((5, 'conn5.g6'), (7, 'conn7.g6')):
        gs = nx.read_graph6('/home/user/Manuscripts/data/' + f)
        fails = {}
        sets = {}
        tested = {}
        for Gx in gs:
            Ev = even_set(Gx)
            if not Ev:
                continue
            if max(d for _, d in Gx.subgraph(Ev).degree()) > 3:
                continue
            G = as_dict(Gx)
            e = len(Ev)
            for y in Ev:
                tested[e] = tested.get(e, 0) + 1
                if floor_with_end(G, y) is None:
                    fails[e] = fails.get(e, 0) + 1
                    if is_set(Gx):
                        sets[e] = sets.get(e, 0) + 1
        print(f'  N={N}: tested (G,y) by e: {dict(sorted(tested.items()))}; failures by e: '
              f'{dict(sorted(fails.items()))}; of which SET: {dict(sorted(sets.items()))}')


if __name__ == '__main__':
    parts = sys.argv[1:] or ['1', '2', '3', '4']
    print('Section 3 counterexamples (exact.py)')
    for p in parts:
        {'1': part1, '2': part2, '3': part3, '4': part4}[p]()

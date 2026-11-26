"""A11: Remark 15(iii) of bs-prescribed. Does the bowtie case hold WITHOUT the (u, v) hypothesis?
Hosts here have NO pair of adjacent odd vertices u ~ v with N(u) & T != {} and N(v) & T = {}
(equivalently: every odd vertex without a T-neighbour has only T-free odd neighbours, so the
component structure of the T-free part never touches the T-adjacent part). Exhaustive on the
connected graphs of order 7; random at orders 9 and 11 with every odd vertex adjacent to T."""
import itertools, random
import networkx as nx
from exact import realise
from counterexamples import even_set, as_dict, le_paths

def is_bowtie(H):
    if H.number_of_nodes() != 5 or H.number_of_edges() != 6: return False
    return sorted(d for _, d in H.degree()) == [2, 2, 2, 2, 4] and nx.number_of_edges(H.subgraph([v for v in H if H.degree(v) == 2])) == 2

def has_uv(G, T):
    for u in G:
        if u in T or not (set(G[u]) & T): continue
        for v in G[u]:
            if v not in T and not (set(G[v]) & T): return True
    return False

n7 = nouv7 = 0
for Gx in nx.read_graph6('/home/user/Manuscripts/data/conn7.g6'):
    Ev = even_set(Gx)
    if len(Ev) != 5 or not is_bowtie(Gx.subgraph(Ev)): continue
    n7 += 1
    T = set(Ev)
    if not has_uv(Gx, T): nouv7 += 1
    assert le_paths(as_dict(Gx), 3) is not None, nx.to_graph6_bytes(Gx)
print(f'order 7: {n7} connected graphs with bowtie even subgraph ({nouv7} without (u,v)); all have p <= 3')

rng = random.Random(7)
T = list('xabcd'); BT = [('x','a'),('x','b'),('x','c'),('x','d'),('a','b'),('c','d')]
for N in (9, 11):
    done = 0
    while done < 60:
        X = ['e%d' % i for i in range(N - 5)]
        G = nx.Graph(BT); G.add_nodes_from(X)
        p = rng.uniform(0.2, 0.5)
        for a, b in itertools.combinations(X, 2):
            if rng.random() < p: G.add_edge(a, b)
        for w in X:
            for t in T:
                if rng.random() < p: G.add_edge(w, t)
            if not set(G[w]) & set(T): G.add_edge(w, rng.choice(T))
        # parity: T even (toggle T-X edges), X odd (toggle X-X edges); keep every X vertex on T
        for t in T:
            if G.degree(t) % 2:
                w = rng.choice(X)
                if G.has_edge(t, w) and len(set(G[w]) & set(T)) > 1: G.remove_edge(t, w)
                elif not G.has_edge(t, w): G.add_edge(t, w)
        bad = [w for w in X if G.degree(w) % 2 == 0]
        for a, b in zip(bad[::2], bad[1::2]):
            if G.has_edge(a, b): G.remove_edge(a, b)
            else: G.add_edge(a, b)
        if sorted(even_set(G)) != sorted(T) or not is_bowtie(G.subgraph(T)) or not nx.is_connected(G): continue
        if has_uv(G, set(T)) or G.number_of_edges() > 26: continue
        assert le_paths(as_dict(G), (N - 1) // 2) is not None, nx.to_graph6_bytes(G)
        done += 1
    print(f'order {N}: 60 random connected bowtie hosts without (u,v) (every odd vertex sees T); all satisfy the floor')

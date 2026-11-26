import random, sys, itertools
from common import *
from circ import solve_circ
rng = random.Random(int(sys.argv[1])); N = int(sys.argv[2]); extra = int(sys.argv[3])
done = bad = 0; kinds = {}
while done < N:
    n = 11 + extra
    w = 0; A = [1, 2, 3, 4, 5]; F = [6, 7, 8, 9, 10]; Y = list(range(11, n))
    G = nx.Graph(); G.add_nodes_from(range(n))
    G.add_edges_from((w, v) for v in A + F)
    kind = rng.choice(['clique', 'indep', 'mixed'])
    for a, b in itertools.combinations(F, 2):
        if kind == 'clique' or (kind == 'mixed' and rng.random() < 0.5): G.add_edge(a, b)
    for a, b in itertools.combinations(A, 2):
        if rng.random() < 0.6: G.add_edge(a, b)
    for x in F + Y:
        for y in A + Y:
            if x != y and not (x in F and y in F) and rng.random() < 0.45: G.add_edge(x, y)
    want = {v: (0 if v <= 5 else 1) for v in G}
    wrong = [v for v in G if G.degree(v) % 2 != want[v]]
    if len(wrong) % 2: continue
    rng.shuffle(wrong); okf = True
    for p, q in zip(wrong[::2], wrong[1::2]):
        if p == w or q == w or (p in F and q in F): okf = False; break
        if p <= 5 and q <= 5 and not Y: okf = False; break
        if p <= 5 and q <= 5:
            y = rng.choice(Y)
            for z in (p, q):
                if G.has_edge(y, z): G.remove_edge(y, z)
                else: G.add_edge(y, z)
        else:
            if G.has_edge(p, q): G.remove_edge(p, q)
            else: G.add_edge(p, q)
    if not okf: continue
    if any(G.degree(v) % 2 != want[v] for v in G) or not nx.is_connected(G): continue
    if set(G.neighbors(w)) != set(A + F): continue
    if kind == 'mixed':
        e = G.subgraph(F).number_of_edges()
        if e in (0, 10): continue
    done += 1; kinds[kind] = kinds.get(kind, 0) + 1
    st, P = solve_circ(G, n // 2, mins={w: 2}, workers=1, time_limit=900)
    if P is None: bad += 1; print('FAIL', kind, sorted(G.edges()), st, flush=True)
    else: assert verify_partition(G, P)
print('D10 rooted test at w: n=%d' % (11 + extra), kinds, 'failures', bad, flush=True)

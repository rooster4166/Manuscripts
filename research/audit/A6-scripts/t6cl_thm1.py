import itertools, random, sys
from common import *
U = list(range(6))
def build(types, Fedges):
    G = nx.complete_graph(6)
    for i, h in enumerate(types):
        x = 6 + i
        G.add_node(x)
        for u in U:
            if u != h: G.add_edge(x, u)
    G.add_edges_from(Fedges)
    return G
def check(G, T, m):
    want = {v: 1 for v in G if v >= 6}
    for u in U: want[u] = 2 if u in T else 0
    from circ import solve_circ
    st, P = solve_circ(G, (m + 6) // 2, exact=want, workers=2, time_limit=900)
    if P is not None:
        assert verify_partition(G, P)
    return st, (len(P) if P else None)
def even_graphs(nX):
    pairs = list(itertools.combinations(range(nX), 2))
    for s in range(1 << len(pairs)):
        E = [pairs[i] for i in range(len(pairs)) if s >> i & 1]
        deg = [0] * nX
        for a, b in E: deg[a] += 1; deg[b] += 1
        if all(d % 2 == 0 for d in deg): yield E
if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'm6':
        # all even F on 6 labelled exterior vertices up to S6 (types are 0..5, one each)
        seen = set(); reps = []
        perms = list(itertools.permutations(range(6)))
        for E in even_graphs(6):
            key = min(tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in E)) for p in perms)
            if key not in seen: seen.add(key); reps.append(E)
        print('even F classes on 6 vertices:', len(reps), flush=True)
        bad = 0; n = 0
        for E in reps:
            G = build(list(range(6)), [(6 + a, 6 + b) for a, b in E])
            for T in itertools.combinations(U, 3):
                st, cnt = check(G, T, 6); n += 1
                if st not in ('OPTIMAL', 'FEASIBLE'):
                    bad += 1; print('FAIL', E, T, st, flush=True)
        print('m=6 checked', n, 'failures', bad, flush=True)
    else:
        rng = random.Random(int(sys.argv[2])); N = int(sys.argv[3])
        bad = 0
        for it in range(N):
            types = [0, 0, 0, 1, 2, 3, 4, 5]
            rng.shuffle(types)
            Es = list(even_graphs(8)) if False else None
            # random even graph on 8 vertices: random graph then fix by symmetric difference with cycles
            pairs = list(itertools.combinations(range(8), 2))
            E = set(p for p in pairs if rng.random() < rng.uniform(0.2, 0.8))
            deg = [0] * 8
            for a, b in E: deg[a] += 1; deg[b] += 1
            odd = [v for v in range(8) if deg[v] % 2]
            rng.shuffle(odd)
            for a, b in zip(odd[::2], odd[1::2]):
                e = tuple(sorted((a, b)))
                if e in E: E.remove(e)
                else: E.add(e)
            G = build(types, [(6 + a, 6 + b) for a, b in E])
            assert all(G.degree(v) % 2 == (0 if v < 6 else 1) for v in G)
            T = tuple(sorted(rng.sample(U, 3)))
            st, cnt = check(G, T, 8)
            if st not in ('OPTIMAL', 'FEASIBLE'):
                bad += 1; print('FAIL', types, sorted(E), T, st, flush=True)
        print('m=8 random checked', N, 'failures', bad, flush=True)

import random, sys, itertools
from common import *
def random_decomp(G, rng):
    rem = set(frozenset(e) for e in G.edges())
    paths = []
    while rem:
        e = rng.choice(sorted(rem, key=lambda f: tuple(sorted(f))))
        a, b = tuple(e); rem.discard(e)
        P = [a, b]
        # extend at both ends randomly
        for _ in range(2):
            while True:
                end = P[-1]
                opts = [w for w in G.neighbors(end) if w not in P and frozenset((end, w)) in rem]
                if not opts or rng.random() < 0.15: break
                w = rng.choice(opts); rem.discard(frozenset((end, w))); P.append(w)
            P.reverse()
        paths.append(tuple(P))
    return paths
def ends(paths, nodes):
    b = {v: 0 for v in nodes}
    for P in paths: b[P[0]] += 1; b[P[-1]] += 1
    return b
def check(seed, mode):
    rng = random.Random(seed)
    n = rng.randint(5, 8)
    p = rng.uniform(0.3, 0.8)
    G = nx.gnp_random_graph(n, p, seed=rng.randint(0, 10**9))
    if G.number_of_edges() < 3: return None
    D = random_decomp(G, rng)
    assert verify_partition(G, D)
    b = ends(D, G.nodes())
    v = rng.choice(list(G.nodes()))
    non = [u for u in G.nodes() if u != v and not G.has_edge(u, v)]
    if not non: return None
    S = rng.sample(non, rng.randint(1, len(non)))
    Z = sum(1 for w in G.neighbors(v) if b[w] == 0)
    tot = sum(b[u] for u in S)
    if mode == 'strict' and not tot > Z: return None
    if mode == 'equal' and not tot == Z: return None
    for u in S:
        if b[u] == 0: continue
        G2 = G.copy(); G2.add_edge(u, v)
        want = dict(b); want[u] -= 1; want[v] += 1
        res = solve(G2, exact_ends=want, workers=1, time_limit=60)
        if res.status in ('OPTIMAL', 'FEASIBLE'):
            assert len(res.paths) == len(D)
            return ('ok', seed, u)
    return ('NONE', seed, n, sorted(G.edges()), D, v, S, Z, tot)
if __name__ == '__main__':
    mode = sys.argv[1]; N = int(sys.argv[2]); start = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    from collections import Counter
    c = Counter(); bad = []
    s = start; tested = 0
    while tested < N:
        r = check(s, mode); s += 1
        if r is None: continue
        tested += 1; c[r[0]] += 1
        if r[0] == 'NONE': bad.append(r)
    print(mode, dict(c))
    for x in bad[:3]: print(x)

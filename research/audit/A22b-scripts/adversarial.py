"""adversarial.py (audit A22b): instances built to put short cycles everywhere the LOCAL hypothesis
of Theorem 6.1 allows: on the inner vertices of the shortest path, on the exceptional vertex v of
the k = 2 five-cycle case, on the other neighbours of a, b, x, y, on second neighbours, ...

Construction: ends a, b, x, y (edges ab, xy); a core joining them (k = 1: edge ya; k = 2: the
5-cycle a v x y p1, or a single path y p1 a; k = 3: path y p1 p2 a, optionally a second one);
random tree-like padding; then "gadgets" (triangle, 4-cycle, K4 minus an edge, K4) hung on
random non-end vertices (each gadget meets the old graph in one vertex, so it creates no cycle
through an end); random extra edges between non-end vertices, kept only if the local hypothesis
survives; parity repaired by pendant leaves (which create no cycles).

Every resulting graph is fed to localproof.run_graph (all pairs satisfying the local hypothesis,
all orientations, all shortest walks; optional brute force of the conclusion).

usage: adversarial.py COUNT SEED [bf]
"""
import sys, random, signal
from localproof import run_graph, new_stats, on_short_cycle, _alarm


def build(rng):
    adj = {}

    def add(u, v):
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)

    nv = [0]

    def new():
        nv[0] += 1
        adj.setdefault(nv[0] - 1, set())
        return nv[0] - 1

    a, b, x, y = new(), new(), new(), new()
    add(a, b); add(x, y)
    ends = {a, b, x, y}
    kind = rng.choice(['k1', 'k2five', 'k2path', 'k3', 'k3double'])
    if kind == 'k1':
        add(y, a)
    elif kind == 'k2five':
        v, p1 = new(), new()
        for u, w in ((a, v), (v, x), (y, p1), (p1, a)):
            add(u, w)
    elif kind == 'k2path':
        p1 = new(); add(y, p1); add(p1, a)
    else:
        p1, p2 = new(), new()
        add(y, p1); add(p1, p2); add(p2, a)
        if kind == 'k3double':
            q1, q2 = new(), new()
            add(x, q1); add(q1, q2); add(q2, b)
    # tree-like padding at random vertices (including ends: trees add no cycles)
    for _ in range(rng.randint(0, 6)):
        u = rng.choice(list(adj))
        add(u, new())
    # gadgets on non-end vertices, preferring vertices near the ends
    for _ in range(rng.randint(1, 6)):
        near = [u for u in adj if u not in ends and any(w in ends for w in adj[u])]
        pool = near if near and rng.random() < 0.8 else [u for u in adj if u not in ends]
        if not pool:
            break
        u = rng.choice(pool)
        g = rng.choice(['tri', 'sq', 'k4e', 'k4'])
        if g == 'tri':
            r, s = new(), new(); add(u, r); add(u, s); add(r, s)
        elif g == 'sq':
            r, s, t = new(), new(), new(); add(u, r); add(r, s); add(s, t); add(t, u)
        elif g == 'k4e':
            r, s, t = new(), new(), new()
            for p, q in ((u, r), (u, s), (r, s), (r, t), (s, t)):
                add(p, q)
        else:
            r, s, t = new(), new(), new()
            for p, q in ((u, r), (u, s), (u, t), (r, s), (r, t), (s, t)):
                add(p, q)
    # random extra edges among non-end vertices, kept if the local hypothesis survives
    V = list(adj)
    for _ in range(rng.randint(0, 6)):
        u, w = rng.sample(V, 2)
        if u in ends or w in ends or w in adj[u]:
            continue
        add(u, w)
        n = len(adj)
        A = [[1 if j in adj[i] else 0 for j in range(n)] for i in range(n)]
        bad = on_short_cycle(n, A)
        if any(bad[e] for e in ends):
            adj[u].discard(w); adj[w].discard(u)
    # parity repair by pendant leaves
    for u in list(adj):
        if len(adj[u]) % 2 == 0 and len(adj[u]) > 0:
            add(u, new())
    n = len(adj)
    A = [[1 if j in adj[i] else 0 for j in range(n)] for i in range(n)]
    return kind, n, A


def main():
    signal.signal(signal.SIGALRM, _alarm)
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    use_bf = len(sys.argv) > 3 and sys.argv[3] == 'bf'
    rng = random.Random(seed)
    st = new_stats()
    kinds = {}
    for i in range(count):
        kind, n, A = build(rng)
        if n > 40:
            continue
        kinds[kind] = kinds.get(kind, 0) + 1
        run_graph(n, A, st, use_bf, 'adv%d' % i)
    print('adversarial', count, seed, kinds, st, flush=True)


if __name__ == '__main__':
    main()

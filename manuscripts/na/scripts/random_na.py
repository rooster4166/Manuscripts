"""Random tests of the construction at larger orders.

usage: python3 random_na.py N TRIALS SEED

Random graph G(N, p) with p uniform in [0.15, 0.7]; the even-degree vertices are paired at random and
the edge of each pair toggled, so that every degree becomes odd or zero; then the component of a
random vertex is kept. For every ordered pair (y, x) with x ~ y satisfying the weak hypothesis, and
for one random packed set Y containing x when possible, the construction is run and its output
checked by the independent verifier."""
import random
import sys

import nalib

N, TRIALS, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(SEED)
stats = dict(graphs=0, pairs=0, na=0, weak=0, ok=0, sets=0, sets_ok=0)
for _ in range(TRIALS):
    p = rng.uniform(0.15, 0.7)
    G = {v: set() for v in range(N)}
    for a in range(N):
        for b in range(a + 1, N):
            if rng.random() < p:
                G[a].add(b)
                G[b].add(a)
    ev = [v for v in G if len(G[v]) % 2 == 0]
    rng.shuffle(ev)
    for i in range(0, len(ev), 2):
        a, b = ev[i], ev[i + 1]
        if b in G[a]:
            G[a].remove(b)
            G[b].remove(a)
        else:
            G[a].add(b)
            G[b].add(a)
    assert all(len(G[v]) % 2 == 1 or len(G[v]) == 0 for v in G)
    stats["graphs"] += 1
    for y in G:
        for x in sorted(G[y]):
            stats["pairs"] += 1
            if any(w != x and w not in G[x] for w in G[y]):
                stats["na"] += 1
            H = {v: set(G[v]) - {x} for v in G if v != x}
            comp = next(c for c in nalib.components(H) if y in c)
            if not any(v not in G[x] for v in comp):
                continue
            stats["weak"] += 1
            for method in ("paper", "tjoin"):
                D, W = nalib.na_construct(G, y, {x}, method)
                ok, msg = nalib.check_na_output(G, D, y, {x})
                assert ok, (G, y, x, method, msg)
            stats["ok"] += 1
            # one random packed Y containing x
            Y = {x}
            cand = [v for v in G if v != y and v not in G[y] and v != x]
            rng.shuffle(cand)
            for v in cand:
                if nalib.packed(G, Y | {v}):
                    Y.add(v)
            if len(Y) > 1:
                NY = set()
                for a in Y:
                    NY |= G[a]
                Hs = {v: set(G[v]) - Y for v in G if v not in Y}
                cs = next(c for c in nalib.components(Hs) if y in c)
                if any(v not in NY for v in cs):
                    stats["sets"] += 1
                    D, W = nalib.na_construct(G, y, Y)
                    ok, msg = nalib.check_na_output(G, D, y, Y)
                    assert ok, (G, y, Y, msg)
                    stats["sets_ok"] += 1
print("N=%d seed=%d " % (N, SEED) + " ".join("%s=%d" % kv for kv in stats.items()), flush=True)

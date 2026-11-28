"""gen_cq.py: random route-respecting (query C) instances on all-odd graphs, for cross-checking
ndsolve.h against tools/route_ext.c.  Forests on non-edges; masks {v, p(v)}.
usage: python3 gen_cq.py count seed [nlist]"""
import random, sys
cnt, seed = int(sys.argv[1]), int(sys.argv[2])
ns = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [4, 6, 8]
rng = random.Random(seed)
out = 0
while out < cnt:
    n = rng.choice(ns)
    p = rng.uniform(0.25, 0.8)
    E = {(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p}
    for _ in range(6):
        deg = [0] * n
        for i, j in E: deg[i] += 1; deg[j] += 1
        bad = [v for v in range(n) if deg[v] % 2 == 0]
        if not bad: break
        rng.shuffle(bad)
        for a, b in zip(bad[::2], bad[1::2]):
            e = (min(a, b), max(a, b))
            E.symmetric_difference_update({e})
    deg = [0] * n
    for i, j in E: deg[i] += 1; deg[j] += 1
    if not all(d % 2 == 1 for d in deg): continue
    E = sorted(E)
    par = {}
    def root(u):
        while u in par: u = par[u]
        return u
    for v in rng.sample(range(n), rng.randint(1, n - 1)):
        c = [u for u in range(n) if u != v and (min(u, v), max(u, v)) not in E and root(u) != v]
        if c: par[v] = rng.choice(c)
    masks = [(1 << v) | ((1 << par[v]) if v in par else 0) for v in range(n)]
    print("C %d %d %s %s %s" % (n, len(E), " ".join(f"{u} {v}" for u, v in E), " ".join(["1"] * n), " ".join(map(str, masks))))
    out += 1

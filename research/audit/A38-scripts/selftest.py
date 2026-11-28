"""Self-test of a38lib.decomps against an independent brute force (restricted-growth labelings
of the edges, each class checked to be a path), on random small graphs."""
import random
import sys
from collections import Counter
from a38lib import G, decomps, norm


def is_path_edgeset(es):
    if not es:
        return False
    deg = Counter()
    for u, v in es:
        deg[u] += 1
        deg[v] += 1
    if any(d > 2 for d in deg.values()):
        return False
    if sum(1 for d in deg.values() if d == 1) != 2:
        return False
    # connected
    adj = {}
    for u, v in es:
        adj.setdefault(u, []).append(v)
        adj.setdefault(v, []).append(u)
    s = next(iter(adj))
    seen = {s}
    st = [s]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    return len(seen) == len(adj) and len(es) == len(adj) - 1


def brute(g, maxp):
    m = g.m()
    cnt = 0

    def rec(i, lab, k):
        nonlocal cnt
        if i == m:
            classes = [[g.edges[j] for j in range(m) if lab[j] == c] for c in range(k)]
            if all(is_path_edgeset(c) for c in classes):
                cnt += 1
            return
        for c in range(min(k + 1, maxp)):
            lab.append(c)
            rec(i + 1, lab, max(k, c + 1))
            lab.pop()
    rec(0, [], 0)
    return cnt


def main(seed=1, trials=60):
    rng = random.Random(seed)
    for t in range(trials):
        n = rng.randint(3, 6)
        es = [(u, v) for u in range(n) for v in range(u + 1, n) if rng.random() < 0.5]
        if not es or len(es) > 9:
            continue
        g = G(n, es)
        for p in range(1, 5):
            a = sum(1 for _ in decomps(g, p))
            b = brute(g, p)
            assert a == b, (n, es, p, a, b)
    # K_{2,6}
    k26 = G(8, [(h, y) for h in (0, 1) for y in range(2, 8)])
    print("K26 decompositions into <= 4 paths:", sum(1 for _ in decomps(k26, 4)))
    print("selftest OK")


if __name__ == "__main__":
    main(*(int(x) for x in sys.argv[1:]))

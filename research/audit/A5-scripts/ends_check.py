"""Sanity check of 'absorbing a cycle preserves an assigned start': in every
two-path partition of P u C (P with tails), both ends of P are path ends."""
import random, itertools
from seglib import segments, graph, is_simple, path_orders
random.seed(3)
def two_path_partitions(n, E):
    adj = {v: [] for v in range(n)}
    for i, (a, b) in enumerate(E):
        adj[a].append((b, i)); adj[b].append((a, i))
    m = len(E); full = (1 << m) - 1
    res = []
    def is_path(R):
        deg = {}
        for i in range(m):
            if R >> i & 1:
                a, b = E[i]; deg[a] = deg.get(a, 0) + 1; deg[b] = deg.get(b, 0) + 1
        if not deg or max(deg.values()) > 2: return None
        ends = [v for v, d in deg.items() if d == 1]
        if len(ends) != 2: return None
        # connectivity
        u = ends[0]; left = R; prev = None
        while True:
            nxt = [(w, i) for w, i in adj[u] if left >> i & 1]
            if not nxt: break
            w, i = nxt[0]; left &= ~(1 << i); u = w
        return tuple(ends) if left == 0 else None
    def dfs(s, u, vis, used):
        for w, i in adj[u]:
            if w in vis: continue
            nu = used | (1 << i)
            e2 = is_path(full & ~nu)
            if e2: res.append(((s, w), e2))
            dfs(s, w, vis | {w}, nu)
    for s in range(n): dfs(s, s, {s}, 0)
    return res
checked = 0; bad = 0
for h in (3, 4, 5, 6):
    orders = path_orders(h)
    for trial in range(40):
        o = random.choice(orders); segs = segments(h, o, 'path')
        S = frozenset(i for i in range(len(segs)) if random.random() < 0.4)
        if not is_simple(segs, S): continue
        n, E = graph(h, segs, S)
        # add tails: leaf at first and/or last contact
        ends = []
        for c in (o[0], o[-1]):
            if random.random() < 0.6:
                E = E + [(c, n)]; ends.append(n); n += 1
            else:
                ends.append(c)
        parts = two_path_partitions(n, E)
        if not parts: continue
        checked += 1
        for p1, p2 in parts:
            if not (set(ends) <= set(p1) | set(p2)): bad += 1
print("decomposable instances checked:", checked, "partitions violating end retention:", bad)

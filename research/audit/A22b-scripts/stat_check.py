"""stat_check.py (audit A22b): independent re-derivation of the table "How often Corollary 7.2
applies" (scripts/localgirth_stat.py), with different code and seeds.

- Sampler: own pairing model (uniform perfect matching of the stubs of (4,3,...,3)), rejected
  unless simple; then rejected unless 3-connected (own test: removing any <= 2 vertices leaves the
  graph connected). This is the uniform distribution on labelled simple 3-connected graphs with
  that degree sequence, as is the one of localgirth_stat.py.
- Hypothesis evaluated through the criterion after Corollary 7.2 (distances in J - z and short
  cycles of J - z through a, b, c, d), not by building J*; the global row through girth of J*.
- Also: how often each single pairing is admissible (non-adjacent pairs) and qualifies.

usage: stat_check.py COUNT SEED n1 n2 ...
"""
import sys, random, itertools
from collections import deque

INF = 10 ** 6


def sample(rng, n):
    degs = [4] + [3] * (n - 1)
    while True:
        stubs = [v for v in range(n) for _ in range(degs[v])]
        rng.shuffle(stubs)
        adj = [set() for _ in range(n)]
        ok = True
        for i in range(0, len(stubs), 2):
            u, v = stubs[i], stubs[i + 1]
            if u == v or v in adj[u]:
                ok = False
                break
            adj[u].add(v); adj[v].add(u)
        if ok and three_connected(adj):
            return adj


def connected_without(adj, removed):
    n = len(adj)
    start = next(v for v in range(n) if v not in removed)
    seen = {start}
    q = deque([start])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if w not in removed and w not in seen:
                seen.add(w); q.append(w)
    return len(seen) == n - len(removed)


def three_connected(adj):
    n = len(adj)
    if not connected_without(adj, set()):
        return False
    for u in range(n):
        if not connected_without(adj, {u}):
            return False
    for u, v in itertools.combinations(range(n), 2):
        if not connected_without(adj, {u, v}):
            return False
    return True


def dist(adj, s, t, removed):
    if s == t:
        return 0
    d = {s: 0}
    q = deque([s])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if w in removed or w in d:
                continue
            d[w] = d[u] + 1
            if w == t:
                return d[w]
            q.append(w)
    return INF


def on_short(adj, s, removed):
    """s on a cycle of length <= 4 of the graph adj minus `removed` (edge-deletion distance test)."""
    for u in adj[s]:
        if u in removed:
            continue
        # distance s -> u avoiding the edge su
        d = {s: 0}
        q = deque([s])
        found = False
        while q and not found:
            x = q.popleft()
            if d[x] >= 3:
                continue
            for w in adj[x]:
                if w in removed or (x == s and w == u) or w in d:
                    continue
                d[w] = d[x] + 1
                if w == u:
                    found = True
                    break
                q.append(w)
        if found:
            return True
    return False


def main():
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    for n in map(int, sys.argv[3:]):
        g_loc = g_glob = pairs = loc_pairs = 0
        for _ in range(count):
            adj = sample(rng, n)
            z = 0  # vertex of degree 4 is vertex 0 by construction
            assert len(adj[z]) == 4
            a, b, c, d = sorted(adj[z])
            rem = {z}
            H_bad = {s: on_short(adj, s, rem) for s in (a, b, c, d)}
            H_girth5 = not any(on_short(adj, s, rem) for s in range(n) if s != z)
            D = lambda u, v: dist(adj, u, v, rem)
            ok_l = ok_g = False
            for (p, q), (r, s) in (((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c))):
                if q in adj[p] or s in adj[r]:
                    continue
                pairs += 1
                reach = D(p, r) < INF or D(p, s) < INF or D(q, r) < INF or D(q, s) < INF
                crit = (not any(H_bad[t] for t in (p, q, r, s)) and D(p, q) >= 4 and D(r, s) >= 4
                        and D(p, r) + D(q, s) >= 3 and D(p, s) + D(q, r) >= 3)
                if crit and reach:
                    loc_pairs += 1
                    ok_l = True
                    if H_girth5:
                        ok_g = True
            g_loc += ok_l
            g_glob += ok_g
        print(f'n={n} graphs={count} pairings={pairs} local_ok_pairings={loc_pairs} '
              f'graphs_local={g_loc} ({100 * g_loc / count:.1f}%) graphs_girth5={g_glob} '
              f'({100 * g_glob / count:.1f}%)', flush=True)


if __name__ == '__main__':
    main()

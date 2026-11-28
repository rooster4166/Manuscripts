"""R2 strengthening by the exact solver (faster than brute force):
some Lovasz decomposition has Q(y) avoiding x AND x y as the terminal edge of Q(x).
Search: Q(x) = x y ... z (a path of length >= 2 ending at an odd vertex z), then exact.avoid_exact on
the rest decides whether the path at y can avoid x (every vertex then needs d mod 2 ends in the rest,
which is exactly the Lovasz condition for the whole decomposition)."""
import sys
import nalib, exact

def r2_good(G, y, x):
    E = frozenset(frozenset((a, b)) for a in G for b in G[a])
    odd = set(v for v in G if len(G[v]) % 2 == 1)
    stack = [([x, y], frozenset([frozenset((x, y))]))]
    while stack:
        P, used = stack.pop()
        cur = P[-1]
        for c in G[cur]:
            if c in P:
                continue
            nu = used | {frozenset((cur, c))}
            Q = P + [c]
            if c in odd:
                rest = {v: set() for v in G}
                for e in E - nu:
                    a, b = tuple(e)
                    rest[a].add(b); rest[b].add(a)
                if len(rest[y]) % 2 == 1 and exact.avoid_exact(rest, y, {x}) is not None:
                    return True
            stack.append((Q, nu))
    return False

tot = good = 0
for line in sys.stdin:
    G = nalib.g6_decode(line)
    if any(len(G[v]) % 2 == 0 for v in G):
        continue
    exact.decomposable.cache_clear()
    for y in G:
        for x in G[y]:
            if not any(w != x and w not in G[x] for w in G[y]):
                continue
            tot += 1
            if r2_good(G, y, x):
                good += 1
            else:
                print("R2 FAILS", line.strip(), y, x, flush=True)
print("NA instances", tot, "R2-strong good", good, flush=True)

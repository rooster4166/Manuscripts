"""example42.py: check Example 4.2 of re-tight (K8 - M, graph6 G]~v~w, r = 0, s = 1) by hand-coded
checks, and the arithmetic of Proposition 4.1 / Example 4.2 for small k."""
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
from g6 import parse_g6  # noqa: E402

n, adj = parse_g6("G]~v~w")
M = sorted({tuple(sorted((v, w))) for v in range(n) for w in range(n) if v != w and w not in adj[v]})
print("non-edges of G]~v~w (the matching M):", M)
assert all(len(a) == 6 for a in adj) and len(M) == 4
r, s = 0, 1
assert s not in adj[r]
N = sorted(adj[r])
fam = {2: [2, 1, 3, 4, 6, 5, 7], 3: [3, 5, 1, 4, 2, 6], 4: [4, 7, 1, 6, 3], 5: [5, 2, 7, 3], 6: [6], 7: [7]}
pairs = [(3, 7), (5, 6)]
assert sorted(fam) == N
used = set()
for x, P in fam.items():
    assert P[0] == x and len(set(P)) == len(P) and r not in P
    for u, v in zip(P, P[1:]):
        assert v in adj[u], (x, u, v)
        e = frozenset((u, v))
        assert e not in used
        used.add(e)
mG = sum(len(adj[v] - {r}) for v in range(n) if v != r) // 2
assert len(used) == mG, (len(used), mG)
seen = set()
for x, y in pairs:
    assert not set(fam[x]) & set(fam[y]) and x not in seen and y not in seen
    seen |= {x, y}
single = [x for x in N if x not in seen]
print("family OK: partition of E(G) (%d edges), pairs disjoint, singletons %s" % (mG, single))
paths = [list(reversed(fam[x])) + [r] + fam[y] for x, y in pairs] + [list(reversed(fam[x])) + [r] for x in single]
E = set()
ends = [0] * n
for P in paths:
    assert len(set(P)) == len(P)
    for u, v in zip(P, P[1:]):
        assert v in adj[u] and frozenset((u, v)) not in E
        E.add(frozenset((u, v)))
    ends[P[0]] += 1
    ends[P[-1]] += 1
assert len(E) == sum(len(a) for a in adj) // 2
print("reassembled: %d paths, e(r) = %d, ends per vertex %s" % (len(paths), ends[r], ends))
endcnt = {v: sum((P[0] == v) + (P[-1] == v) for P in fam.values() if len(P) > 1) for v in range(n)}
print("ends of nontrivial members per vertex:", endcnt)
# Prop 4.1 arithmetic
for k in range(2, 12):
    lhs = 2 * (2 * k - 2) + (k - 3) * (2 * k - 3)
    assert lhs == 2 * k * k - 5 * k + 5
    assert (2 * k * k - 3 * k + 4) - (2 * k - 2) == 2 * k * k - 5 * k + 6
    comp = k * (2 * k - 1) - (2 * k * k - 3 * k + 4)
    assert comp == 2 * k - 4
    cp = k * (2 * k - 1) - k - (2 * k - 2)
    assert cp == 2 * (k - 1) ** 2
print("Prop 4.1 / Ex 4.2 arithmetic OK for k = 2..11")
# max edges of an even-degree graph of order 2k with a vertex of degree 2k-2 is k(2k-1) - k (K_2k - M)
for k in range(2, 6):
    print("k=%d: threshold 2k^2-3k+4 = %d, m(K_2k - M) = %d" % (k, 2 * k * k - 3 * k + 4, 2 * k * k - 2 * k))

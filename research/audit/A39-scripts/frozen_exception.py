"""A39: Test1 at the one frozen root where the method fails (Huv]z~}, r = 2; G = B - r = K_7).
Construction: a Hamilton decomposition C1, C2, C3 of K_7 (Walecki) with x1x2 in C1 (x1, x2 the two
neighbours of r in B), x2w in C2, wv in C3 (v != x1).  Paths: C1 - x1x2, (C2 - x2w) + x2r,
C3 - wv, and r x1 x2 w v.  Four paths = k, two ends at r.  Checked from scratch."""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from g6 import parse_g6
from verify_drm import check_B

g, r = 'Huv]z~}', 2
n, adj = parse_g6(g)
z = [v for v in range(n) if len(adj[v]) % 2 == 0][0]
B = {v: set(adj[v]) - {z} for v in range(n) if v != z}
k = len(B) // 2
V7 = sorted(v for v in B if v != r)
x1, x2 = sorted(B[r])
assert all(b in B[a] for a, b in itertools.combinations(V7, 2))     # G = K_7
# Walecki: vertices inf, 0..5 ; cycle i: inf, i, i+1, i-1, i+2, i-2, i+3 (mod 6)
lab = V7
def cyc(i):
    seq = [i % 6, (i + 1) % 6, (i - 1) % 6, (i + 2) % 6, (i - 2) % 6, (i + 3) % 6]
    return ['inf'] + seq
best = None
for perm in itertools.permutations(V7):
    m = {'inf': perm[0]}
    for j in range(6):
        m[j] = perm[j + 1]
    C = [[m[v] for v in cyc(i)] for i in range(3)]
    E = [set(frozenset(e) for e in zip(c, c[1:] + c[:1])) for c in C]
    e12 = frozenset((x1, x2))
    for a in range(3):
        if e12 not in E[a]:
            continue
        for b in range(3):
            if b == a:
                continue
            c3 = 3 - a - b
            for w in V7:
                if w in (x1, x2) or frozenset((x2, w)) not in E[b]:
                    continue
                for v in V7:
                    if v in (x1, x2, w) or frozenset((w, v)) not in E[c3]:
                        continue
                    def cut(c, e):
                        i = [j for j in range(7) if frozenset((c[j], c[(j + 1) % 7])) == e][0]
                        return c[i + 1:] + c[:i + 1]
                    P1 = cut(C[a], e12)
                    P2 = cut(C[b], frozenset((x2, w)))
                    P2 = P2 if P2[-1] == x2 else P2[::-1]
                    P3 = cut(C[c3], frozenset((w, v)))
                    paths = [P1, P2 + [r], P3, [r, x1, x2, w, v]]
                    err = check_B(B, paths, r, k)
                    print('paths:', paths, '->', 'OK (k = %d paths, 2 ends at r)' % k if err is None else err)
                    sys.exit(0)
print('no construction found')

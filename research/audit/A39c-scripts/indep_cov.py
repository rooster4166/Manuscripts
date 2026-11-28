"""A39c: independent recount of Theorem A / Theorem B coverage at order 9 (no networkx, own graph6
parser).  Theorem B is evaluated literally from the hypotheses of the Lean statements
`exists_decomp_of_connector` (delta = 0) and `exists_decomp_of_connector_mid` (delta = 1): every
path Q of G = B - r (any length) with ends q1 != q2 in N and at most one other vertex in N; parity
`every x in N odd in G - E(Q)` checked, not assumed; lambda = sum over V(Q) of ceil(d_{G'}(v)/2).
Also: the 24/21/3/23 split of the roots with no connector, the 28 roots needing length 3, their
membership in multi-token's unscheduled set, and the claim that the parity hypothesis is automatic.
usage (from the repo root): python3 -I research/audit/A39c-scripts/indep_cov.py"""
import sys
from collections import Counter, deque

ROOT = sys.argv[1] if len(sys.argv) > 1 else '.'
J9 = ROOT + '/manuscripts/multi-token/data/J9_d6.g6'
NONE = ROOT + '/manuscripts/multi-token/data/runs/J9_none.txt'


def g6(s):
    d = [ord(c) - 63 for c in s.strip()]
    n = d[0]; bits = []
    for x in d[1:]:
        bits += [(x >> (5 - i)) & 1 for i in range(6)]
    adj = [set() for _ in range(n)]; p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]: adj[i].add(j); adj[j].add(i)
            p += 1
    return adj


def paths(adj, verts, a, b):
    """all simple paths from a to b inside verts"""
    out = []
    def go(p, seen):
        u = p[-1]
        if u == b: out.append(list(p)); return
        for w in adj[u]:
            if w in verts and w not in seen:
                seen.add(w); p.append(w); go(p, seen); p.pop(); seen.discard(w)
    go([a], {a}); return out


def dist(adj, verts, a, b):
    D = {a: 0}; q = deque([a])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if w in verts and w not in D: D[w] = D[u] + 1; q.append(w)
    return D.get(b)


unsched = {}
for line in open(NONE):
    f = line.split(); unsched[f[0]] = {int(x) for x in f[1].split(',')}

C = Counter(); new28 = []; nolist = []
for line in open(J9):
    s6 = line.split()[0]; adjJ = g6(s6); n = len(adjJ); k = (n - 1) // 2
    z = [v for v in range(n) if len(adjJ[v]) % 2 == 0]; assert len(z) == 1; z = z[0]
    Z = adjJ[z]
    VB = set(range(n)) - {z}
    adjB = [adjJ[v] - {z} for v in range(n)]
    dB = lambda v: len(adjB[v])
    for r in sorted(Z):
        if len(adjJ[r]) != n - 2: continue
        C['roots'] += 1
        uns = r in unsched.get(s6, ())
        C['unsched'] += uns
        VG = VB - {r}
        N = adjB[r]
        s = [v for v in VG if v not in N]; assert len(s) == 1; s = s[0]
        dG = {v: len(adjB[v] & VG) for v in VG}
        h = lambda t, excl: sum(1 for x in N if x not in excl and dB(x) >= 2 * t)
        if s not in Z:
            # Theorem A: at most one vertex of positive even degree in G
            ev = [v for v in VG if dG[v] % 2 == 0 and dG[v] > 0]
            eps = 1 if any(dG[x] % 2 == 0 for x in N) else 0
            okA = len(ev) <= 1 and all(
                (h(t, ()) + eps) // 2 + t <= k + 1 or h(t + 1, ()) // 2 + eps + 2 * t <= k + 1
                for t in range(3, k))
            C['A'] += okA; C['A unsched'] += okA and uns
            continue
        C['sinZ'] += 1
        T = [v for v in VB if v not in Z]; assert len(T) == 2 and set(T) <= N
        okB = {1: False, 2: False, 3: False}; anyQ = False; lens = set()
        for q1 in N:
            for q2 in N:
                if q1 >= q2: continue
                for Q in paths(adjB, VG, q1, q2):
                    others = [v for v in Q[1:-1] if v in N]
                    if len(others) > 1: continue
                    delta = len(others)
                    E = {frozenset(e) for e in zip(Q, Q[1:])}
                    dGp = {v: dG[v] - sum(1 for e in E if v in e) for v in VG}
                    if not all(dGp[x] % 2 == 1 for x in N): continue      # Lean hodd
                    # admissible connector: the ends must be the two even N-vertices T
                    assert {q1, q2} == set(T), (s6, r, Q)
                    assert len(Q) - 1 <= 2 + delta, (s6, r, Q)              # length bound
                    assert all(v == s for v in Q[1:-1] if v not in N)
                    anyQ = True; lens.add(len(Q) - 1)
                    lam = sum((dGp[v] + 1) // 2 for v in set(Q))
                    VQ = set(Q)
                    ok = all((h(t, VQ) + delta) // 2 + (1 if t <= lam else 0) + t <= k + 1 or
                             (h(t + 1, VQ) + delta) // 2 + (1 if t <= lam else 0) + 2 * t <= k + 1
                             for t in range(3, k))
                    if ok: okB[len(Q) - 1] = True
        # every path q1 ... q2 with <= 1 interior N-vertex satisfies parity (Cor. 4.2 remark)
        q1, q2 = T
        for Q in paths(adjB, VG, q1, q2):
            if sum(1 for v in Q[1:-1] if v in N) <= 1:
                E = {frozenset(e) for e in zip(Q, Q[1:])}
                assert all((dG[x] - sum(1 for e in E if x in e)) % 2 == 1 for x in N)
        b12 = okB[1] or okB[2]; b = b12 or okB[3]
        C['B<=2'] += b12; C['B'] += b; C['B unsched'] += b and uns; C['B<=2 unsched'] += b12 and uns
        if b and not b12:
            new28.append((s6, r, uns, dist(adjB, VG, q1, q2), sorted(lens)))
        if not anyQ:
            d = dist(adjB, VG, q1, q2)
            h7 = sum(1 for x in N if len(adjJ[x]) == 7)
            # connectors in the sense of Sec. 4 (any q1-q2 path) still exist: least delta among them
            mind = min(sum(1 for v in Q[1:-1] if v in N) for Q in paths(adjB, VG, q1, q2))
            nolist.append((s6, r, d, h7, mind))
        elif not b:
            C['B cond fails'] += 1
print(dict(C))
print('A|B', C['A'] + C['B'], ' A|B<=2', C['A'] + C['B<=2'],
      ' unsched A|B', C['A unsched'] + C['B unsched'], ' unsched A|B<=2', C['A unsched'] + C['B<=2 unsched'])
print('outside A|B:', C['roots'] - C['A'] - C['B'], '= noQ', len(nolist), '+ cond',
      C['roots'] - C['A'] - C['B'] - len(nolist))
print('roots needing length 3:', len(new28), ' unscheduled:', sum(x[2] for x in new28),
      ' dist:', Counter(x[3] for x in new28))
print('no connector:', len(nolist), ' by distance', Counter(x[2] for x in nolist),
      ' with <=2 deg-7 nbrs of r:', sum(1 for x in nolist if x[3] <= 2),
      ' least delta of a q1-q2 path:', Counter(x[4] for x in nolist))
with open(ROOT + '/research/audit/A39c-scripts/new28.txt', 'w') as fh:
    for x in new28: fh.write('%s %d\n' % (x[0], x[1]))

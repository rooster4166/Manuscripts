#!/usr/bin/env python3
"""Audit A39b: the order-9 roots that the Lean `delta = 1` theorem certifies only through a
connector of length 3 (q1 y s q2 or q1 s y q2), classified by dist_G(q1, q2), and whether they are
multi-token-unscheduled (multi-token/data/runs/J9_none.txt)."""
import importlib.util, sys
from collections import Counter, deque
here = '/home/user/Manuscripts/research/audit/A39b-scripts/'
spec = importlib.util.spec_from_file_location('m', here + 'lean_hyp_cov.py')
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
fn = sys.argv[1]; none_fn = sys.argv[2]
unsched = {}
for line in open(none_fn):
    f = line.split(); unsched[f[0]] = {int(x) for x in f[1].split(',')}
def dist(G, a, b):
    D = {a: 0}; q = deque([a])
    while q:
        u = q.popleft()
        for w in G[u]:
            if w not in D: D[w] = D[u] + 1; q.append(w)
    return D.get(b)
C = Counter(); listing = []
for ln, line in enumerate(open(fn), 1):
    g = line.split()[0]
    n, J = m.g6(line); k = (n - 1) // 2
    z = [v for v in range(n) if len(J[v]) % 2 == 0][0]; Z = set(J[z])
    V = [v for v in range(n) if v != z]; B = {v: set(J[v]) - {z} for v in V}
    dB = {v: len(B[v]) for v in V}
    for r in sorted(Z):
        if len(J[r]) != n - 2: continue
        N = set(B[r]); s = [v for v in V if v != r and v not in N][0]
        if s not in Z: continue
        G = {v: set(B[v]) - {r} for v in V if v != r}
        T = [v for v in V if v not in Z]; q1, q2 = T
        lens = set()
        for Q in m.paths_between_N(G, N, 7):
            EQ = {frozenset(e) for e in zip(Q, Q[1:])}
            dGp = {v: len(G[v]) - sum(1 for e in EQ if v in e) for v in G}
            if any(dGp[x] % 2 == 0 for x in N): continue
            inner = [v for v in Q[1:-1] if v in N]
            if len(inner) > 1: continue
            d = len(inner); lam = sum((dGp[v] + 1) // 2 for v in Q)
            Nt = [x for x in N if x not in Q]; h = lambda t: sum(1 for x in Nt if 2 * t <= dB[x])
            if all((h(t) + d) // 2 + (1 if t <= lam else 0) + t <= k + 1 or
                   (h(t + 1) + d) // 2 + (1 if t <= lam else 0) + 2 * t <= k + 1 for t in range(3, k)):
                lens.add(len(Q) - 1)
                assert {Q[0], Q[-1]} == {q1, q2}
        if lens and max(lens) == 3 and min(lens) == 3:
            dd = dist(G, q1, q2)
            us = r in unsched.get(g, set())
            C[('dist', dd)] += 1; C[('unscheduled', us)] += 1
            listing.append((ln, g, z, r, dd, us))
print(dict(C))
for x in listing: print(*x)

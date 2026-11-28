#!/usr/bin/env python3
"""Audit A39b: recount, at order 9 and s in Z, the roots with dist_G(q1,q2) >= 3 (paper: 52 = 49 + 3),
and the Theorem-B counts on multi-token's unscheduled roots with and without length-3 connectors
(paper: 1,041 with length <= 2)."""
import importlib.util, sys
from collections import Counter, deque
here = '/home/user/Manuscripts/research/audit/A39b-scripts/'
spec = importlib.util.spec_from_file_location('m', here + 'lean_hyp_cov.py')
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
fn, none_fn = sys.argv[1], sys.argv[2]
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
C = Counter()
for line in open(fn):
    g = line.split()[0]; n, J = m.g6(line); k = (n - 1) // 2
    z = [v for v in range(n) if len(J[v]) % 2 == 0][0]; Z = set(J[z])
    V = [v for v in range(n) if v != z]; B = {v: set(J[v]) - {z} for v in V}
    dB = {v: len(B[v]) for v in V}
    for r in sorted(Z):
        if len(J[r]) != n - 2: continue
        us = r in unsched.get(g, set())
        C[('unsched roots', us)] += 1
        N = set(B[r]); s = [v for v in V if v != r and v not in N][0]
        if s not in Z: continue
        G = {v: set(B[v]) - {r} for v in V if v != r}
        q1, q2 = [v for v in V if v not in Z]
        C[('sinZ dist', dist(G, q1, q2))] += 1
        le2 = any3 = False
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
                any3 = True
                if len(Q) <= 3: le2 = True
        if us: C[('unsched B len<=2', le2)] += 1; C[('unsched B any (Lean)', any3)] += 1
for kk in sorted(C, key=str): print(kk, C[kk])

# ---- distance-3 roots: is there a Lean-admissible connector at all (q1 y s q2 / q1 s y q2)?
C3 = Counter()
for line in open(fn):
    g = line.split()[0]; n, J = m.g6(line); k = (n - 1) // 2
    z = [v for v in range(n) if len(J[v]) % 2 == 0][0]; Z = set(J[z])
    V = [v for v in range(n) if v != z]; B = {v: set(J[v]) - {z} for v in V}
    for r in sorted(Z):
        if len(J[r]) != n - 2: continue
        N = set(B[r]); s = [v for v in V if v != r and v not in N][0]
        if s not in Z: continue
        G = {v: set(B[v]) - {r} for v in V if v != r}
        q1, q2 = [v for v in V if v not in Z]
        if dist(G, q1, q2) != 3: continue
        adm = False
        for Q in m.paths_between_N(G, N, 3):
            if len(Q) == 4 and {Q[0], Q[-1]} == {q1, q2} and s in Q[1:-1]: adm = True
        C3[('dist-3 root has a q1-y-s-q2 / q1-s-y-q2 connector', adm)] += 1
for kk in sorted(C3, key=str): print(kk, C3[kk])

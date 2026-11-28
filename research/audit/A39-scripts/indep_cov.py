"""A39: independent recount of the Theorem A / Theorem B degree conditions and of the collection's
hypotheses at roots of degree n-2 (no networkx, no code shared with thm_cov.py / coverage.py).

Theorem B connectors are enumerated generically: every path Q of G = B - r of length 1 or 2 with
both ends in N such that every vertex of N is odd in G - E(Q) (the theorem's hypothesis), without
using T or Z.

usage: indep_cov.py J9      (order 9 table, the 1,597 unscheduled roots, the 154 split)
       indep_cov.py resid   (residual families)
"""
import sys, itertools
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from g6 import parse_g6, J_from_resid

ROOT = '/home/user/Manuscripts/manuscripts'


def setup(n, adj):
    ev = [v for v in range(n) if len(adj[v]) % 2 == 0]
    if len(ev) != 1:
        return None
    z = ev[0]
    Z = set(adj[z])
    VB = [v for v in range(n) if v != z]
    dB = {v: len(adj[v] - {z}) for v in VB}
    return z, Z, VB, dB


def root_data(n, adj, z, Z, VB, dB, r):
    k = len(VB) // 2
    N = [x for x in VB if x != r and x in adj[r]]
    nonN = [x for x in VB if x != r and x not in adj[r]]
    assert len(nonN) == 1 and len(N) == 2 * k - 2
    s = nonN[0]
    VG = [v for v in VB if v != r]
    dG = {v: len(adj[v] - {z, r}) for v in VG}
    return k, N, s, VG, dG


def thmA(k, N, s, VG, dG, dB):
    if any(dB[x] < 2 for x in N):
        return None
    posev = [v for v in VG if dG[v] > 0 and dG[v] % 2 == 0]
    if len(posev) > 1:
        return None
    eps = 1 if any(dG[x] % 2 == 0 for x in N) else 0
    h = lambda t: sum(1 for x in N if dB[x] >= 2 * t)
    for t in range(3, k):
        if not ((h(t) + eps) // 2 + t <= k + 1 or h(t + 1) // 2 + eps + 2 * t <= k + 1):
            return False
    return True


def connectors(adj, z, r, N, VG, dG):
    Nset = set(N)
    out = []
    G = {v: adj[v] - {z, r} for v in VG}
    # length 1
    for a, b in itertools.combinations(N, 2):
        if b in G[a]:
            out.append((a, b))
    # length 2
    for a, b in itertools.combinations(N, 2):
        for y in VG:
            if y in (a, b):
                continue
            if y in G[a] and y in G[b]:
                out.append((a, y, b))
    good = []
    for Q in out:
        loss = Counter()
        for u, v in zip(Q, Q[1:]):
            loss[u] += 1
            loss[v] += 1
        if all((dG[x] - loss[x]) % 2 == 1 for x in N):
            good.append((Q, loss))
    return good


def thmB(adj, z, r, k, N, s, VG, dG, dB, only_delta0=False):
    if any(dB[x] < 2 for x in N):
        return None
    good = connectors(adj, z, r, N, VG, dG)
    if not good:
        return 'noQ'
    Nset = set(N)
    for Q, loss in good:
        delta = 1 if (len(Q) == 3 and Q[1] in Nset) else 0
        if only_delta0 and delta:
            continue
        lam = sum(-(-(dG[v] - loss[v]) // 2) for v in Q)
        Nt = [x for x in N if x not in Q]
        ht = lambda t: sum(1 for x in Nt if dB[x] >= 2 * t)
        ok = True
        for t in range(3, k):
            q = 1 if lam >= t else 0
            if not ((ht(t) + delta) // 2 + q + t <= k + 1 or
                    (ht(t + 1) + delta) // 2 + q + 2 * t <= k + 1):
                ok = False
                break
        if ok:
            return True
    return False


def connected(VB, adjB):
    seen = {VB[0]}
    st = [VB[0]]
    while st:
        v = st.pop()
        for w in adjB[v]:
            if w not in seen:
                seen.add(w); st.append(w)
    return len(seen) == len(VB)


def mr_conditions(n, adj, z, VB, dB, r, k):
    adjB = {v: adj[v] - {z} for v in VB}
    univ = [v for v in VB if dB[v] == 2 * k - 1]
    m47 = len(univ) >= k - 1
    m74 = min(dB.values()) >= 2 * k - 3
    # Thm 166: R contains r, |R| = k, all of B-degree >= 2k-2; u universal in R; b on X = V - R
    m166 = False
    if connected(VB, adjB):
        H = [v for v in VB if dB[v] >= 2 * k - 2 and v != r]
        for Rr in itertools.combinations(H, k - 1):
            R = set(Rr) | {r}
            u = sum(1 for v in R if dB[v] == 2 * k - 1)
            X = [v for v in VB if v not in R]
            lo = sum(dB[v] % 2 for v in X)                       # least sum of b
            hi = sum(min(dB[v], 2 * k - dB[v]) - ((min(dB[v], 2 * k - dB[v]) - dB[v]) % 2)
                     for v in X)                                  # largest sum with parity
            # each b_v ranges over {d mod 2, d mod 2 + 2, ..., cap_v}: sums hit every value of the
            # right parity between lo and hi
            if lo <= u <= hi and (u - lo) % 2 == 0:
                m166 = True
                break
    # Thm 50
    m50 = False
    for c in range(1, int(2 * k / 15) + 1):
        if len(univ) >= k - c:
            for R in itertools.combinations(univ, k - c):
                X = [v for v in VB if v not in R]
                eX = sum(1 for a, b in itertools.combinations(X, 2) if b in adjB[a])
                if eX <= k * k / 8:
                    m50 = True
                    break
        if m50:
            break
    return m47, m74, m166, m50


def dist_G(adj, z, r, VG, a, b):
    G = {v: adj[v] - {z, r} for v in VG}
    d = {a: 0}
    fr = [a]
    while fr:
        nf = []
        for v in fr:
            for w in G[v]:
                if w not in d:
                    d[w] = d[v] + 1; nf.append(w)
        fr = nf
    return d.get(b, None)


def run_J9():
    lines = [l.split()[0] for l in open(ROOT + '/multi-token/data/J9_d6.g6') if l.strip()]
    unsched = {}
    for l in open(ROOT + '/multi-token/data/runs/J9_none.txt'):
        f = l.split()
        unsched[f[0]] = set(int(x) for x in f[1].split(','))
    C = Counter()
    split = Counter()
    rows = []
    uns_total = 0
    for g in lines:
        n, adj = parse_g6(g)
        st = setup(n, adj)
        z, Z, VB, dB = st
        C['graphs'] += 1
        C['d(z)=%d' % len(Z)] += 1
        for r in sorted(Z):
            if len(adj[r]) != n - 2:
                continue
            k, N, s, VG, dG = root_data(n, adj, z, Z, VB, dB, r)
            a = thmA(k, N, s, VG, dG, dB)
            b = thmB(adj, z, r, k, N, s, VG, dG, dB)
            b0 = thmB(adj, z, r, k, N, s, VG, dG, dB, only_delta0=True)
            m47, m74, m166, m50 = mr_conditions(n, adj, z, VB, dB, r, k)
            mr = m47 or m74 or m166 or m50
            sinZ = s in Z
            uns = g in unsched and r in unsched[g]
            nev = sum(1 for v in VG if dG[v] % 2 == 0)
            keys = ['roots', 'sinZ' if sinZ else 'snotZ', 'nevG=%d' % nev]
            if a is True: keys.append('A')
            if b0 is True: keys.append('B0')
            if b is True: keys.append('B')
            if a is True or b is True: keys.append('A|B')
            if m47: keys.append('MR47')
            if m74: keys.append('MR74')
            if m166: keys.append('MR166')
            if m50: keys.append('MR50')
            if mr: keys.append('MRany')
            if mr and not (a is True or b is True): keys.append('MR\\(A|B)')
            if a is True or b is True or mr: keys.append('A|B|MR')
            for key in keys:
                C[key] += 1
                if not sinZ: C['snotZ:' + key] += 1
                if uns: C['uns:' + key] += 1
            rows.append((g, r, sinZ, a, b, b0, m47, m74, m166, m50))
            if not (a is True or b is True):
                h7 = sum(1 for x in N if len(adj[x]) == 7)
                kind = 'noQ' if b == 'noQ' else 'cond'
                if kind == 'noQ':
                    T = [v for v in VB if v not in Z]
                    dd = dist_G(adj, z, r, VG, T[0], T[1])
                    split[('noQ', 'dist=%s' % dd)] += 1
                split[(kind, 'sinZ' if sinZ else 'snotZ', 'h7=%d' % h7)] += 1
    for key in sorted(C):
        print(key, C[key])
    print('--- outside A and B')
    for key in sorted(split):
        print(key, split[key])
    return rows


def run_resid():
    files = ['resid_O8', 'resid_O10', 'e28_hard', 'clt_hard']
    for f in files:
        C = Counter()
        for l in open(ROOT + '/multi-token/data/%s.g6' % f):
            if not l.strip():
                continue
            n, adj = J_from_resid(l.split()[0])
            st = setup(n, adj)
            if st is None:
                C['bad'] += 1; continue
            z, Z, VB, dB = st
            C['graphs'] += 1
            for r in sorted(Z):
                if len(adj[r]) != n - 2:
                    continue
                k, N, s, VG, dG = root_data(n, adj, z, Z, VB, dB, r)
                a = thmA(k, N, s, VG, dG, dB)
                b = thmB(adj, z, r, k, N, s, VG, dG, dB)
                m47, m74, m166, m50 = mr_conditions(n, adj, z, VB, dB, r, k)
                nev = sum(1 for v in VG if dG[v] % 2 == 0)
                C['roots'] += 1
                C['n=%d' % n] += 1
                C['d(z)=%d' % len(Z)] += 1
                C['nevG=%d' % nev] += 1
                C['A=%s' % a] += 1
                C['B=%s' % b] += 1
                C['MR47'] += m47; C['MR74'] += m74; C['MR166'] += m166; C['MR50'] += m50
                C['|V(B)-N(z)|=%d' % (len(VB) - len(Z))] += 1
        print(f, dict(sorted(C.items())))


if __name__ == '__main__':
    if sys.argv[1] == 'J9':
        run_J9()
    else:
        run_resid()

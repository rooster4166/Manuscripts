"""tjoin.py -- Lemma S (static steering) by the T-join criterion, compared with the exact trail
search static_steer of cov.py on every joint path of every order-8 instance."""
import sys, collections, random
from multiprocessing import Pool
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
from cov import static_steer, ekey

def tjoin_ok(n, E, g, h):
    A = [set() for _ in range(n)]
    for u, v in E: A[u].add(v); A[v].add(u)
    X = A[h] | {h}
    if g not in X:
        return crit(n, A, X, g)
    # g ~ h: first move g -> u with u not in N[h], then the criterion for (u, h)
    for u in A[g]:
        if u in X: continue
        E2 = E - {ekey(g, u)}
        if len(A[u]) == 1: return True     # retires at once
        A2 = [set() for _ in range(n)]
        for a, b in E2: A2[a].add(b); A2[b].add(a)
        if crit(n, A2, X, u): return True
    return False

def crit(n, A, X, g):
    VH = set(range(n)) - X | {g}
    for t in VH:
        if not A[t]: continue
        if any(w in X and w != g for w in A[t]): continue
        if t == g and any(w in X for w in A[g]): continue
        T = set(A[t]) ^ {g} if t != g else set(A[g])
        # components of H - t, H = K[VH]
        rest = VH - {t}; seen = set(); ok = True
        for s in rest:
            if s in seen: continue
            comp = {s}; st = [s]; seen.add(s)
            while st:
                x = st.pop()
                for y in A[x]:
                    if y in rest and y not in seen: seen.add(y); comp.add(y); st.append(y)
            if len(comp & T) % 2: ok = False; break
        if ok: return True
    return False

def work(line):
    inst, rest = line.split(' | ')
    t = inst.split(); n, adj = g6_decode(t[0]); c1,a1,c2,a2 = map(int,t[1:5])
    E0 = frozenset(ekey(u, v) for u in range(n) for v in adj[u])
    C = collections.Counter()
    for r in rest.split():
        o, P, kind, res = r.split(':')
        if kind != 'a' or o != '0': continue
        P = tuple(map(int, P.split('-')))
        E = E0 - set(ekey(p, q) for p, q in zip(P, P[1:]))
        d = collections.Counter()
        for u, v in E: d[u] += 1; d[v] += 1
        if d[c1] == 0 or d[c2] == 0: continue
        for g, h in ((c1, c2), (c2, c1)):
            a = static_steer(n, E, g, h); b = tjoin_ok(n, E, g, h)
            C[(a, b)] += 1
    return C

if __name__ == '__main__':
    C = collections.Counter()
    lines = open('pall8.out').readlines()
    random.seed(5); lines = random.sample(lines, 6000)
    with Pool(4) as pool:
        for c in pool.imap_unordered(work, lines, chunksize=20): C.update(c)
    print('(trail search, T-join criterion):', dict(C))

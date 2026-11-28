"""sched.py -- k-token schedules (multi-token moves M, D, S) for L_N(2) instances, with the final
state allowed to have at most one token and any number of live tails (the MTL2 'fin').
State: frozenset of edges, tuple of live tails.  Tails (c, s, x): leaf c at stem s avoiding x.
Reads lines 'g6 c1 a1 c2 a2' (F all odd); builds K = F + c1 l1 + c2 l2."""
import sys
from functools import lru_cache
from lnlib import g6_decode

def run(n, adj, c1, a1, c2, a2, fin_tails=2, maxdepth=60, fin='mtl2'):
    E = set()
    for u in range(n):
        for v in adj[u]:
            if u < v: E.add((u, v))
    tl = []
    N = n
    for (c, a) in ((c1, a1), (c2, a2)):
        if len(adj[c]) == 1 and a not in adj[next(iter(adj[c]))]:
            tl.append((c, next(iter(adj[c])), a))
        else:
            E.add((c, N)); tl.append((N, c, a)); N += 1
    tails0 = tuple(tl)
    def degs(E):
        d = [0] * N
        for u, v in E: d[u] += 1; d[v] += 1
        return d
    def nbrs(E):
        A = [set() for _ in range(N)]
        for u, v in E: A[u].add(v); A[v].add(u)
        return A
    seen = {}
    def ok_fin(E, tails):
        d = degs(E)
        tok = [v for v in range(N) if d[v] > 0 and d[v] % 2 == 0]
        if len(tok) > 1 or len(tails) > fin_tails:
            return False
        if fin == 'sparse':
            # Theorem A: the avoided vertices of the live tails form a sparse set
            A = nbrs(E)
            xs = set(x for (c, s_, x) in tails)
            for v in range(N):
                if len(A[v] & xs) > 1:
                    return False
        return True
    def search(E, tails, depth):
        key = (E, tails)
        if key in seen: return seen[key]
        seen[key] = False
        if ok_fin(E, tails):
            seen[key] = True; return True
        if depth == 0: return False
        d = degs(E); A = nbrs(E)
        tok = [v for v in range(N) if d[v] > 0 and d[v] % 2 == 0]
        X = set()
        for (c, s, x) in tails: X |= {c, x}
        tokset = set(tok)
        # M: token move
        for p in tok:
            for u in A[p]:
                if d[u] % 2 == 0 or u in X: continue
                if any(w in tokset and w != p for w in A[u] if w != p): continue
                E2 = E - {(min(p, u), max(p, u))}
                if search(E2, tails, depth - 1):
                    seen[key] = True; return True
        # D: drop a live tail with odd stem
        for i, (c, s, x) in enumerate(tails):
            if d[s] % 2 == 1:
                E2 = E - {(min(c, s), max(c, s))}
                t2 = tails[:i] + tails[i + 1:]
                if search(E2, t2, depth - 1):
                    seen[key] = True; return True
        # S: suppression of a degree-2 token
        leaves = {c for (c, s, x) in tails}
        for p in tok:
            if d[p] != 2: continue
            a, b = sorted(A[p])
            if b in A[a] or a in leaves or b in leaves: continue
            if any({a, b} == {x, s} for (c, s, x) in tails): continue
            E2 = (E - {(min(p, a), max(p, a)), (min(p, b), max(p, b))}) | {(a, b)}
            if search(frozenset(E2), tails, depth - 1):
                seen[key] = True; return True
        return False
    return search(frozenset(E), tails0, maxdepth)

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'mtl2'
    tot = cov = 0
    for line in sys.stdin:
        t = line.split()
        if not t: continue
        n, adj = g6_decode(t[0])
        c1, a1, c2, a2 = map(int, t[1:5])
        r = run(n, adj, c1, a1, c2, a2, fin=mode)
        tot += 1; cov += r
        if not r: print('NOSCHED', line.strip(), flush=True)
    print('total', tot, 'scheduled', cov, file=sys.stderr)

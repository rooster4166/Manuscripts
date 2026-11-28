"""schedules for L_N(m) (any m) with fin 'old' (<=1 token, <=1 live tail) or 'sparse' (Theorem A:
<=1 token, live heads sparse).  Reads 'g6 c1 a1 c2 a2 ...'."""
import sys
from lnlib import g6_decode
def run(n, adj, pairs, fin):
    E = set((u, v) for u in range(n) for v in adj[u] if u < v)
    tl = []; N = n
    for (c, a) in pairs:
        if len(adj[c]) == 1 and a not in adj[next(iter(adj[c]))]:
            tl.append((c, next(iter(adj[c])), a))
        else:
            E.add((c, N)); tl.append((N, c, a)); N += 1
    seen = {}
    def degs(E):
        d = [0] * N
        for u, v in E: d[u] += 1; d[v] += 1
        return d
    def nbrs(E):
        A = [set() for _ in range(N)]
        for u, v in E: A[u].add(v); A[v].add(u)
        return A
    def ok_fin(E, tails):
        d = degs(E)
        if sum(1 for v in range(N) if d[v] > 0 and d[v] % 2 == 0) > 1: return False
        if fin == 'old': return len(tails) <= 1
        A = nbrs(E); xs = set(x for (_, _, x) in tails)
        return all(len(A[v] & xs) <= 1 for v in range(N))
    def search(E, tails, depth):
        key = (E, tails)
        if key in seen: return seen[key]
        seen[key] = False
        if ok_fin(E, tails): seen[key] = True; return True
        if depth == 0: return False
        d = degs(E); A = nbrs(E)
        tok = [v for v in range(N) if d[v] > 0 and d[v] % 2 == 0]; ts = set(tok)
        X = set()
        for (c, s, x) in tails: X |= {c, x}
        for p in tok:
            for u in A[p]:
                if d[u] % 2 == 0 or u in X: continue
                if any(w in ts and w != p for w in A[u] if w != p): continue
                if search(E - {(min(p, u), max(p, u))}, tails, depth - 1): seen[key] = True; return True
        for i, (c, s, x) in enumerate(tails):
            if d[s] % 2 == 1:
                if search(E - {(min(c, s), max(c, s))}, tails[:i] + tails[i+1:], depth - 1): seen[key] = True; return True
        leaves = {c for (c, s, x) in tails}
        for p in tok:
            if d[p] != 2: continue
            a, b = sorted(A[p])
            if b in A[a] or a in leaves or b in leaves: continue
            if any({a, b} == {x, s} for (c, s, x) in tails): continue
            E2 = (E - {(min(p, a), max(p, a)), (min(p, b), max(p, b))}) | {(a, b)}
            if search(frozenset(E2), tails, depth - 1): seen[key] = True; return True
        return False
    return search(frozenset(E), tuple(tl), 80)
if __name__ == '__main__':
    res = {'old': 0, 'sparse': 0}; tot = 0
    for line in sys.stdin:
        t = line.split()
        if not t: continue
        n, adj = g6_decode(t[0]); v = list(map(int, t[1:]))
        pairs = list(zip(v[0::2], v[1::2]))
        tot += 1
        for f in res: res[f] += run(n, adj, pairs, f)
    print('total', tot, res)

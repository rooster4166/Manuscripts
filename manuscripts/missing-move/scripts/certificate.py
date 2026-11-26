"""Print a winning certificate (strategy tree) of the Fan game with path insertion.

Usage: python3 certificate.py GRAPH6 ROOT KMAX [nonp]
The moves are those of fan_game.py with option np: single and grouped Fan transfers, and new
paths of any length made of held edges ("nonp" restricts new paths to single edges). Grouped
transfers branch over the adversary's donor; every branch is printed."""
import sys
from functools import lru_cache
from itertools import combinations
import networkx as nx

def certify(G, r, kmax, newpath=True):
    n = G.number_of_nodes()
    E = sorted(tuple(sorted(e)) for e in G.edges())
    nbr = [0] * n
    for a, b in E:
        nbr[a] |= 1 << b; nbr[b] |= 1 << a
    popc = lambda x: bin(x).count("1")

    @lru_cache(maxsize=None)
    def win(rem, b):
        s = sum(b)
        if not rem:
            return ("END",) if (s <= n and b[r] >= 1) else None
        remmask = [0] * n
        for a, c in rem:
            remmask[a] |= 1 << c; remmask[c] |= 1 << a
        zero = sum(1 << v for v in range(n) if b[v] == 0)
        Z = lambda u: popc(nbr[u] & ~remmask[u] & zero)
        for (a, c) in sorted(rem):
            rest = rem - {(a, c)}
            for u, t in ((a, c), (c, a)):
                if b[t] > Z(u):
                    nb = list(b); nb[u] += 1; nb[t] -= 1
                    sub = win(rest, tuple(nb))
                    if sub: return ("single", t, u, b[t], Z(u), tuple(nb), sub)
        if s + 2 <= n:
            radj = {}
            for a, c in rem:
                radj.setdefault(a, []).append(c); radj.setdefault(c, []).append(a)
            def dfs(path, used):
                if len(path) >= 2 and (newpath or len(path) == 2):
                    nb = list(b); nb[path[0]] += 1; nb[path[-1]] += 1
                    sub = win(rem - used, tuple(nb))
                    if sub: return ("newpath", tuple(path), tuple(nb), sub)
                for w in radj.get(path[-1], []):
                    if w in path: continue
                    e = (min(path[-1], w), max(path[-1], w))
                    x = dfs(path + [w], used | {e})
                    if x: return x
                return None
            for v0 in sorted(radj):
                x = dfs([v0], frozenset())
                if x: return x
        for u in range(n):
            cands = [t for t in range(n) if (min(u, t), max(u, t)) in rem]
            if len(cands) < 2: continue
            z = Z(u)
            for k in range(2, len(cands) + 1):
                for T in combinations(cands, k):
                    if sum(b[t] for t in T) <= z: continue
                    branches = []
                    for t in T:
                        if b[t] == 0: continue
                        nb = list(b); nb[u] += 1; nb[t] -= 1
                        sub = win(rem - {(min(u, t), max(u, t))}, tuple(nb))
                        if not sub: break
                        branches.append((t, tuple(nb), sub))
                    else:
                        return ("grouped", u, T, sum(b[t] for t in T), z, branches)
        return None

    def starts(F):
        Fs = set(F); deg = [0] * n
        for a, c in E:
            if (a, c) not in Fs: deg[a] += 1; deg[c] += 1
        poseven = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
        out = []
        if len(poseven) <= 1: out.append(("lovasz", tuple(d % 2 for d in deg)))
        if all(d > 0 for d in deg):
            ev = [v for v in range(n) if deg[v] % 2 == 0]
            if len(ev) == 2:
                for u, v in (ev, ev[::-1]):
                    b = [d % 2 for d in deg]; b[v] = 2; b[u] = 0
                    out.append(("lemma3", tuple(b)))
        return out

    for k in range(kmax + 1):
        for F in combinations(E, k):
            for kind, b0 in starts(F):
                c = win(frozenset(F), b0)
                if c: return F, kind, b0, c
    return None

def show(c, ind=0):
    pad = "  " * ind
    if c[0] == "END": print(pad + "END"); return
    if c[0] == "single":
        _, t, u, bt, z, nb, sub = c
        print(pad + f"single {t}->{u}  (b(t)={bt} > Z(u)={z})  b={nb}"); show(sub, ind)
    elif c[0] == "newpath":
        _, p, nb, sub = c
        print(pad + f"new path {p}  b={nb}"); show(sub, ind)
    else:
        _, u, T, sm, z, br = c
        print(pad + f"grouped at {u}, T={T} (sum={sm} > Z={z}); adversary picks:")
        for t, nb, sub in br:
            print(pad + f"  donor {t}: b={nb}"); show(sub, ind + 2)

if __name__ == "__main__":
    G = nx.from_graph6_bytes(sys.argv[1].encode())
    r = int(sys.argv[2]); kmax = int(sys.argv[3])
    d = dict(G.degree()); print("deg", d)
    res = certify(G, r, kmax, newpath=len(sys.argv) < 5)
    if not res: print("no certificate"); sys.exit()
    F, kind, b0, c = res
    print("held F =", F, "seed", kind, b0); show(c)

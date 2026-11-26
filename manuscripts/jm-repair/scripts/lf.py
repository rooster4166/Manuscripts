"""Core utilities for linear-forest decompositions of K_m and the two-vertex
extension problem (TVL) used in the repair of Javadi-Miralaei Theorem 8.

A decomposition is a dict colour[(u,v)] -> i for u<v in range(m), colours 0..n-1.
"""
import itertools, random
from collections import defaultdict

def edges_by_colour(m, n, col):
    E = [[] for _ in range(n)]
    for (u, v), i in col.items():
        E[i].append((u, v))
    return E

def is_linear_forest(nv, edges):
    deg = defaultdict(int)
    parent = list(range(nv))
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    for u, v in edges:
        deg[u] += 1; deg[v] += 1
        if deg[u] > 2 or deg[v] > 2:
            return False
        ru, rv = find(u), find(v)
        if ru == rv:
            return False
        parent[ru] = rv
    return True

def components(m, edges):
    """Components of a linear forest on range(m): list of (end1, end2); end1==end2 for trivial."""
    adj = defaultdict(list)
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    seen = set(); comps = []
    for v in range(m):
        if v in seen or len(adj[v]) == 2:
            continue
        # v is an end (deg 0 or 1)
        if len(adj[v]) == 0:
            seen.add(v); comps.append((v, v)); continue
        prev, cur = None, v
        seen.add(v)
        while True:
            nxt = [w for w in adj[cur] if w != prev]
            if not nxt:
                break
            prev, cur = cur, nxt[0]
            seen.add(cur)
        comps.append((v, cur))
    assert len(seen) == m, "not a linear forest (cycle?)"
    return comps

def pvec(m, n, col):
    E = edges_by_colour(m, n, col)
    return [m - len(E[i]) for i in range(n)]

def check_decomp(m, n, col):
    assert len(col) == m * (m - 1) // 2
    E = edges_by_colour(m, n, col)
    return all(is_linear_forest(m, E[i]) for i in range(n))

# ---------- demands for the two-vertex step ----------
def tvl_demands(p, K, U, c):
    """delta_i = number of new edges (attachments) required in colour i (xy excluded)."""
    d = []
    for i, pi in enumerate(p):
        if i == c:
            d.append(max(0, pi + 3 - K))
        elif i in U:
            d.append(max(0, pi + 5 - K))
        else:
            d.append(max(0, pi + 4 - K))
    return d

def hall_check_Z(m, n, col, U, c, K=None, want_witness=False):
    """Check (UH-Z) and (LH-Z) for all B subset of V. Returns (ok_UH, ok_LH, witness)."""
    if K is None:
        K = 2 * n + 1 - m
    p = pvec(m, n, col)
    d = tvl_demands(p, K, U, c)
    E = edges_by_colour(m, n, col)
    comps = [components(m, E[i]) for i in range(n)]
    # bitmask of slots: for each colour, list of (mask_end1, mask_end2)
    ok_UH = ok_LH = True; wit = None
    full = (1 << m) - 1
    for B in range(1 << m):
        nb = bin(B).count("1")
        tot_up = 0; tot_low = 0
        for i in range(n):
            N = 0; two = 0
            for (u, w) in comps[i]:
                su = (B >> u) & 1; sw = (B >> w) & 1
                s = su + sw
                if s >= 1: N += 1
                if s == 2: two += 1
            psi = N + (1 if (two >= 1 and i != c) else 0)
            kap = 2 if i == c else 4
            tot_up += min(kap, psi)
            tot_low += max(0, d[i] - psi)
        if 2 * nb > tot_up:
            ok_UH = False; wit = wit or ("UH", B)
        if tot_low > 2 * (m - nb):
            ok_LH = False; wit = wit or ("LH", B)
        if not want_witness and not (ok_UH and ok_LH):
            break
    return ok_UH, ok_LH, wit

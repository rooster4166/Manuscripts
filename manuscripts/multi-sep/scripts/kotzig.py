"""Cubic MSEP via Kotzig decompositions: perfect matching M of K, orientation of each cycle of
the 2-factor K - M; path of the M-edge uv is u+ u v v+.  Separation fails only if {u+, v+} is a
pair.  Test whether some (M, orientation) separates."""
import random, sys, subprocess, itertools
import msl
from g6 import g6_to_adj

def perfect_matchings(K, limit=None):
    V = sorted(K); out = []
    M = {}
    def rec():
        if limit and len(out) >= limit: return
        free = [v for v in V if v not in M]
        if not free: out.append(dict(M)); return
        v = free[0]
        for w in sorted(K[v]):
            if w not in M:
                M[v] = w; M[w] = v
                rec()
                del M[v]; del M[w]
    rec(); return out

def cycles_of(K, M):
    seen = set(); cyc = []
    for v in sorted(K):
        if v in seen: continue
        c = [v]; seen.add(v)
        prev, cur = None, v
        while True:
            nb = [w for w in K[cur] if w != M[cur] and w != prev]
            nxt = nb[0] if prev is not None or True else None
            if prev is None: nxt = nb[0]
            else: nxt = [w for w in K[cur] if w != M[cur] and w != prev][0]
            if nxt == v: break
            c.append(nxt); seen.add(nxt); prev, cur = cur, nxt
        cyc.append(c)
    return cyc

def kotzig_ok(K, pairs):
    part = {}
    for a, b in pairs: part[a] = b; part[b] = a
    for M in perfect_matchings(K):
        cyc = cycles_of(K, M)
        cid = {}; pos = {}
        for i, c in enumerate(cyc):
            for j, v in enumerate(c): cid[v] = i; pos[v] = j
        for orient in itertools.product([0, 1], repeat=len(cyc)):
            def succ(v):
                c = cyc[cid[v]]; j = pos[v]
                return c[(j + 1) % len(c)] if orient[cid[v]] == 0 else c[(j - 1) % len(c)]
            ok = True
            for u in K:
                v = M[u]
                if u < v and part.get(succ(u)) == succ(v): ok = False; break
            if ok: return True
    return False

def main(n, ngraphs, per, seed):
    rng = random.Random(seed)
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {n}", shell=True, capture_output=True, text=True).stdout.split()
    rng.shuffle(gs)
    tot = fail = nopm = 0
    for s in gs[:ngraphs]:
        K = g6_to_adj(s)
        if not perfect_matchings(K, limit=1): nopm += 1; continue
        for _ in range(per):
            P = msl.far_pairs(K, rng, perfect_only=True)
            if P is None: continue
            tot += 1
            if not kotzig_ok(K, P):
                fail += 1
                if fail <= 3: print("KOTZIG-FAIL", s, P, flush=True)
    print(f"n={n}: tested {tot}, Kotzig fails {fail}, graphs without PM {nopm}")
main(*map(int, sys.argv[1:5]))

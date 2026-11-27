"""All-odd rotation recursion.  K has all degrees odd (or 0); A a family of distance-3 classes.
Step: choose a cycle C = c_0..c_{r-1} (or a leaf-to-leaf path P = p_0..p_m) and a direction;
K' = K - E(C), classes: c_i joins every class containing c_{i+1}, plus {c_i, c_{i+1}}
(for a path, i = 1..m-1, and the edge p_0 p_1 becomes a new path).  Valid if every new class is a
distance-3 set of K'.  Lift: extend Q_{c_i} by the edge c_i c_{i+1} (rotation of ends)."""
import random, sys, subprocess, itertools
import msl
from coarsen import prune

def simple_cycles(K, maxlen):
    V = sorted(v for v in K if K[v])
    out = []
    for s in V:
        stack = [(s, [s])]
        while stack:
            v, path = stack.pop()
            for w in K[v]:
                if w == s and len(path) >= 3:
                    if path[1] < path[-1]: out.append(list(path))
                elif w > s and w not in path and len(path) < maxlen:
                    stack.append((w, path + [w]))
    return out

def leaf_paths(K, maxlen):
    leaves = [v for v in K if len(K[v]) == 1]
    out = []
    for s in leaves:
        stack = [(s, [s])]
        while stack:
            v, path = stack.pop()
            for w in K[v]:
                if w in path: continue
                if len(K[w]) == 1 and w > s:
                    out.append(path + [w])
                elif len(K[w]) >= 3 and len(path) < maxlen:
                    stack.append((w, path + [w]))
    return out

def valid(K1, A1):
    for S in A1:
        for a in S:
            d = msl.dist(K1, a)
            for b in S:
                if b != a and d.get(b, 99) < 3: return False
    return True

def step(K, A, seq, closed):
    """seq: cycle (closed) or path; returns (K1, A1) or None"""
    K1 = msl.copy(K)
    r = len(seq)
    E = [(seq[i], seq[(i + 1) % r]) for i in range(r if closed else r - 1)]
    for a, b in E: K1[a].discard(b); K1[b].discard(a)
    rot = range(r) if closed else range(1, r - 1)
    succ = {seq[i]: seq[(i + 1) % r] for i in rot}
    A1 = []
    for S in A:
        add = {c for c, s in succ.items() if s in S}
        A1.append(frozenset(S | add))
    for c, s in succ.items(): A1.append(frozenset({c, s}))
    A1 = prune(K1, A1)
    if not valid(K1, A1): return None
    return K1, A1, succ

def solve(K, A, memo, maxlen, budget):
    budget[0] -= 1
    if budget[0] < 0: return None
    A = prune(K, A)
    key = (frozenset((v, frozenset(N)) for v, N in K.items() if N), frozenset(A))
    if key in memo: return memo[key]
    E = msl.edges(K)
    if not E: return []
    if all(len(K[v]) <= 1 for v in K):
        return [[a, b] for a, b in E]
    cands = [(c, True) for c in simple_cycles(K, maxlen)] + [(p, False) for p in leaf_paths(K, maxlen)]
    cands.sort(key=lambda t: len(t[0]))
    res = None
    for seq, closed in cands:
        for sq in (seq, seq[::-1]):
            st = step(K, A, sq, closed)
            if st is None: continue
            K1, A1, succ = st
            D = solve(K1, A1, memo, maxlen, budget)
            if D is None:
                if budget[0] < 0: return None
                continue
            D = [list(P) for P in D]
            own = {c: next(i for i, P in enumerate(D) if P[0] == c or P[-1] == c) for c in succ}
            orig = [list(P) for P in D]
            for c, s in succ.items():
                i = own[c]
                if orig[i][-1] == c: D[i] = D[i] + [s]
                else: D[i] = [s] + D[i]
            if not closed: D.append([sq[0], sq[1]])
            res = D; break
        if res is not None: break
    memo[key] = res
    return res

if __name__ == "__main__":
    from g6 import g6_to_adj
    n = int(sys.argv[1]); flag = sys.argv[2] if len(sys.argv) > 2 else ""
    per = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    maxlen = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    rng = random.Random(1)
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {flag} {n}", shell=True, capture_output=True, text=True).stdout.split()
    rng.shuffle(gs)
    fails = tot = unk = 0
    for s in gs[:300]:
        K = g6_to_adj(s)
        for _ in range(per):
            P = msl.far_pairs(K, rng, perfect_only=True)
            if P is None: continue
            tot += 1
            b = [20000]
            D = solve(msl.copy(K), [frozenset(p) for p in P], {}, maxlen, b)
            if D is None:
                if b[0] < 0: unk += 1
                else:
                    fails += 1
                    print("ROT-FAIL", s, P, flush=True)
            else:
                assert msl.is_decomp(K, D, msl.lovasz_profile(K)), (s, P, D)
                assert msl.separates(D, P)
    print(f"n={n} {flag}: rotation strategy fails {fails}/{tot}, budget-out {unk}")

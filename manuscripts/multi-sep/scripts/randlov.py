"""Randomised constructive search for separating Lovasz decompositions: run Lovasz's induction
(Cases I-III, Fan transfers) with random choices, then random end-swaps; check separation.
Used to certify instances the budgeted exact oracle leaves undecided."""
import random
import msl

def lovasz_random(K, rng):
    """Random Lovasz decomposition of K (at most one positive even vertex)."""
    K = msl.copy(K)
    return _lov(K, rng)

def _lov(K, rng):
    E = msl.edges(K)
    if not E:
        return []
    ev = [v for v in K if K[v] and len(K[v]) % 2 == 0]
    if ev:
        z = ev[0]
        u = rng.choice(sorted(K[z]))
        K[z].discard(u); K[u].discard(z)
        D = _lov(K, rng)
        K[z].add(u); K[u].add(z)
        K1 = msl.copy(K); K1[z].discard(u); K1[u].discard(z)
        chs = msl.fan_chains(D, z, u, K1)
        ch = rng.choice(chs)
        return msl.fan_exec(D, ch, u)
    big = [x for x in K if len(K[x]) >= 3]
    if big:
        x = rng.choice(big); u = rng.choice(sorted(K[x]))
        l = max(K) + 1
        K[x].discard(u); K[u].discard(x); K[l] = {u}; K[u].add(l)
        D = _lov(K, rng)
        K[u].discard(l); del K[l]; K[x].add(u); K[u].add(x)
        # delete leaf l
        D2 = []
        for Q in D:
            if Q[0] == l: Q = Q[1:]
            elif Q[-1] == l: Q = Q[:-1]
            if len(Q) >= 2: D2.append(Q)
        bu = sum((Q[0] == u) + (Q[-1] == u) for Q in D2)
        if bu == 0:
            return D2 + [[u, x]]
        K1 = msl.copy(K); K1[x].discard(u); K1[u].discard(x)
        chs = msl.fan_chains(D2, u, x, K1)
        ch = rng.choice(chs)
        return msl.fan_exec(D2, ch, x)
    # matching
    return [[a, b] for a, b in E]

def end_swaps(K, D, rng, pairs, steps=2000):
    """Random walk on Lovasz decompositions by end-swaps, decreasing the number of violated
    (path, pair) incidences when possible (simple annealing)."""
    def viol(D):
        c = 0
        for Q in D:
            S = set(Q)
            for a, b in pairs:
                if a in S and b in S: c += 1
        return c
    cur = viol(D)
    for _ in range(steps):
        if cur == 0: return D
        # pick a random interior vertex v of a random path P, swap with Q_v
        i = rng.randrange(len(D)); P = D[i]
        if len(P) < 3: continue
        j = rng.randrange(1, len(P) - 1); v = P[j]
        k = next(k for k, Q in enumerate(D) if k != i and (Q[0] == v or Q[-1] == v))
        Q = D[k] if D[k][-1] == v else D[k][::-1]   # Q ends at v
        A, B = P[:j + 1], P[j:]                     # both contain v
        opts = []
        if not (set(Q) & set(B[1:])): opts.append((A, Q + B[1:]))
        if not (set(Q) & set(A[:-1])): opts.append((B, Q + A[::-1][1:]))
        if not opts: continue
        X, Y = rng.choice(opts)
        D2 = [R for t, R in enumerate(D) if t not in (i, k)] + [X, Y]
        nv = viol(D2)
        if nv <= cur or rng.random() < 0.05:
            D, cur = D2, nv
    return D if cur == 0 else None

def find_separating(K, pairs, rng, tries=200):
    for t in range(tries):
        D = lovasz_random(K, rng)
        assert msl.is_decomp(K, D, msl.lovasz_profile(K))
        D = end_swaps(K, D, rng, pairs)
        if D is not None:
            assert msl.is_decomp(K, D, msl.lovasz_profile(K)) and msl.separates(D, pairs)
            return D
    return None

if __name__ == "__main__":
    import sys, ast
    rng = random.Random(1)
    n_ok = n_tot = 0
    for line in open(sys.argv[1]):
        if not line.startswith("UNDECIDED"): continue
        rest = line.split(None, 2)[2]
        i = rest.index("} [")
        K = ast.literal_eval(rest[:i + 1]); pairs = ast.literal_eval(rest[i + 2:])
        K = {int(v): set(N) for v, N in K.items()}
        n_tot += 1
        D = find_separating(K, pairs, rng)
        n_ok += D is not None
        print("certified" if D else "NOT FOUND", len(K), len(pairs), flush=True)
    print("certified", n_ok, "of", n_tot)

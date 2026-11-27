"""Exhaustive coarsening recursion on the small failures (all Case II choices, full backtracking)."""
import random, subprocess, sys
import msl, coarsen
from g6 import g6_to_adj

def solve_all(K, A, memo):
    A = coarsen.prune(K, A)
    key = (frozenset((v, frozenset(N)) for v, N in K.items() if N), frozenset(A))
    if key in memo: return memo[key]
    E = msl.edges(K)
    if not E: memo[key] = []; return []
    res = None
    ev = [v for v in K if K[v] and len(K[v]) % 2 == 0]
    if ev:
        z = ev[0]
        for u in sorted(K[z]):
            K1 = msl.copy(K); K1[z].discard(u); K1[u].discard(z)
            members = set().union(*[S for S in A if u in S]) | {u}
            if not coarsen.far3(K1, z, members): continue
            A1 = [frozenset(S | {z}) if u in S else S for S in A] + [frozenset({u, z})]
            D = solve_all(K1, A1, memo)
            if D is not None:
                D = [list(P) for P in D]
                i = next(i for i, P in enumerate(D) if P[0] == z or P[-1] == z)
                P = D[i]; D[i] = P + [u] if P[-1] == z else [u] + P
                res = D; break
    else:
        big = [x for x in K if len(K[x]) >= 3]
        if not big:
            res = [[a, b] for a, b in E]
        for x in big:
            if res is not None: break
            for u in sorted(K[x]):
                l = max(K) + 1
                H = msl.copy(K); H[x].discard(u); H[u].discard(x); H[l] = {u}; H[u].add(l)
                A1 = [frozenset(S | {l}) if x in S else S for S in A] + [frozenset({x, l})]
                D = solve_all(H, A1, memo)
                if D is not None:
                    res = [[x if v == l else v for v in P] for P in D]; break
    memo[key] = res
    return res

if __name__ == "__main__":
    rng = random.Random(1)
    n = int(sys.argv[1]); flag = sys.argv[2] if len(sys.argv) > 2 else ""
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {flag} {n}", shell=True, capture_output=True, text=True).stdout.split()
    fails = 0; tot = 0
    for s in gs:
        K = g6_to_adj(s)
        for _ in range(3):
            P = msl.far_pairs(K, rng, perfect_only=True)
            if P is None: continue
            tot += 1
            D = solve_all(msl.copy(K), [frozenset(p) for p in P], {})
            if D is None:
                fails += 1
                print("STRATEGY-FAIL", s, P, flush=True)
            else:
                assert msl.is_decomp(K, D, msl.lovasz_profile(K)) and msl.separates(D, P)
    print(f"n={n}: exhaustive coarsening strategy fails on {fails}/{tot}")

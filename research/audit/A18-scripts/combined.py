# Combined certified strategy: Case II (leaf merge), certified Case I, and rotation, mixed freely.
import sys
sys.path.insert(0, "/home/user/Manuscripts/manuscripts/multi-sep/scripts")
import msl, coarsen, rotate
from g6 import g6_to_adj
sys.setrecursionlimit(10000)
def solve(K, A, memo):
    A = coarsen.prune(K, A)
    key = (frozenset((v, frozenset(N)) for v, N in K.items() if N), frozenset(A))
    if key in memo: return memo[key]
    memo[key] = None
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
            D = solve(K1, A1, memo)
            if D is not None:
                D = [list(P) for P in D]
                i = next(i for i, P in enumerate(D) if P[0] == z or P[-1] == z)
                P = D[i]; D[i] = P + [u] if P[-1] == z else [u] + P
                res = D; break
    else:
        if all(len(K[v]) <= 1 for v in K):
            res = [[a, b] for a, b in E]
        # rotations
        if res is None:
            n = len(K)
            cands = [(c, True) for c in rotate.simple_cycles(K, n)] + [(p, False) for p in rotate.leaf_paths(K, n)]
            for seq, closed in cands:
                if res is not None: break
                for sq in (seq, seq[::-1]):
                    st = rotate.step(K, A, sq, closed)
                    if st is None: continue
                    K1, A1, succ = st
                    D = solve(K1, A1, memo)
                    if D is None: continue
                    D = [list(P) for P in D]
                    own = {c: next(i for i, P in enumerate(D) if P[0] == c or P[-1] == c) for c in succ}
                    orig = [list(P) for P in D]
                    for c, s in succ.items():
                        i = own[c]
                        if orig[i][-1] == c: D[i] = D[i] + [s]
                        else: D[i] = [s] + D[i]
                    if not closed: D.append([sq[0], sq[1]])
                    res = D; break
        # Case II
        if res is None:
            for x in [x for x in K if len(K[x]) >= 3]:
                if res is not None: break
                for u in sorted(K[x]):
                    l = max(K) + 1
                    H = msl.copy(K); H[x].discard(u); H[u].discard(x); H[l] = {u}; H[u].add(l)
                    A1 = [frozenset(S | {l}) if x in S else S for S in A] + [frozenset({x, l})]
                    D = solve(H, A1, memo)
                    if D is not None:
                        res = [[x if v == l else v for v in P] for P in D]; break
    memo[key] = res
    return res
for line in sys.stdin:
    s, rest = line.split(None, 1)
    P = eval(rest)
    K = g6_to_adj(s)
    D = solve(msl.copy(K), [frozenset(p) for p in P], {})
    ok = D is not None and msl.is_decomp(K, D, msl.lovasz_profile(K)) and msl.separates(D, P)
    print(s, P, "combined:", "SUCCESS" if ok else ("FAIL" if D is None else "BAD"), flush=True)

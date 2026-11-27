"""The coarsening recursion R(K, A).

K: graph with at most one vertex of positive even degree.  A: family of vertex sets ("classes"),
each a distance-3 set of K (may overlap).  Goal: Lovasz decomposition whose paths meet every class
at most once.

Steps (no Fan transfer with a non-trivial chain is ever needed):
  Case II (all degrees odd, some x with d(x) >= 3, any u in N(x)):
      H = K - ux + u l (new leaf l), classes: l joins every class containing x, plus {x, l}.
      Lift: merge l into x (Q_l avoids x and x's class-mates).
  Case I (one even vertex z, u in N(z)) -- VALID only if z is at distance >= 3 in K - uz from
      every member of every class containing u (including u itself):
      K' = K - uz, classes: z joins every class containing u, plus {u, z}.
      Lift: Q_z avoids u and all of u's class-mates, so append zu.
  Case III (all degrees <= 1): single edges.
Search with backtracking over the choices; report success.
"""
import random, sys
import msl

def far3(K, a, S):
    d = msl.dist(K, a)
    return all(d.get(b, 99) >= 3 for b in S if b != a)

PRUNE = True

def prune(K, A):
    """drop isolated members; drop classes with < 2 live members; dedupe"""
    out = set()
    for S in A:
        T = frozenset(v for v in S if K.get(v))
        if len(T) >= 2:
            out.add(T)
    return list(out)

def solve(K, A, rng, budget):
    """returns decomposition or None; budget: list with remaining node count"""
    if PRUNE:
        A = prune(K, A)
    budget[0] -= 1
    if budget[0] < 0:
        return None
    E = msl.edges(K)
    if not E:
        return []
    ev = [v for v in K if K[v] and len(K[v]) % 2 == 0]
    if ev:
        z = ev[0]
        us = sorted(K[z]); rng.shuffle(us)
        for u in us:
            K1 = msl.copy(K); K1[z].discard(u); K1[u].discard(z)
            members = set().union(*[S for S in A if u in S]) | {u}
            if not far3(K1, z, members):
                continue
            A1 = [S | {z} if u in S else S for S in A] + [frozenset({u, z})]
            A1 = [frozenset(S) for S in A1]
            D = solve(K1, A1, rng, budget)
            if D is None:
                if budget[0] < 0: return None
                continue
            Q = next(i for i, P in enumerate(D) if P[0] == z or P[-1] == z)
            P = D[Q]
            assert u not in P
            D[Q] = P + [u] if P[-1] == z else [u] + P
            return D
        return None
    big = [x for x in K if len(K[x]) >= 3]
    if big:
        rng.shuffle(big)
        for x in big[:3]:
            us = sorted(K[x]); rng.shuffle(us)
            for u in us[:2]:
                l = max(K) + 1
                H = msl.copy(K); H[x].discard(u); H[u].discard(x); H[l] = {u}; H[u].add(l)
                A1 = [frozenset(S | {l}) if x in S else S for S in A] + [frozenset({x, l})]
                D = solve(H, A1, rng, budget)
                if D is None:
                    if budget[0] < 0: return None
                    continue
                out = []
                for P in D:
                    P = [x if v == l else v for v in P]
                    out.append(P)
                return out
        return None
    return [[a, b] for a, b in E]

def run(K, pairs, rng, budget=20000, tries=5):
    A = [frozenset(p) for p in pairs]
    for t in range(tries):
        b = [budget]
        D = solve(msl.copy(K), A, rng, b)
        if D is not None:
            assert msl.is_decomp(K, D, msl.lovasz_profile(K)), D
            assert msl.separates(D, pairs)
            return D
    return None

if __name__ == "__main__":
    import subprocess
    from g6 import g6_to_adj
    n = int(sys.argv[1]); count = int(sys.argv[2]); seed = int(sys.argv[3])
    mind = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    girth = int(sys.argv[5]) if len(sys.argv) > 5 else 3
    rng = random.Random(seed)
    flag = f"-t" if girth >= 4 else ""
    flag = "-f" if girth >= 5 else flag
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {flag} {n}", shell=True, capture_output=True, text=True).stdout.split()
    rng.shuffle(gs)
    ok = tot = 0
    for s in gs[:count]:
        K = g6_to_adj(s)
        P = msl.far_pairs(K, rng, mind=mind, perfect_only=True)
        if P is None: continue
        tot += 1
        D = run(K, P, rng)
        ok += D is not None
    print(f"n={n} mind={mind} girth>={girth}: coarsening recursion succeeded {ok}/{tot}")

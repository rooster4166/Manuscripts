"""Local repair for CL.  K' has one even vertex u; z odd, z not in N[[u]].  For every rainbow
(separating) Lovasz decomposition D' of K' in which Q_z meets [u] at u_i, is there an end-swap at
a vertex v strictly between z and u_i on Q_z that keeps the decomposition rainbow (option 1:
z keeps the shortened prefix)?"""
import random, sys
import msl
from exp_ee import one_even

def swap1(D, z, cls_of, pairs):
    """yield decompositions obtained by option-1 swaps on Q_z before its first [u]-vertex"""
    pass

def main(trials, seed):
    rng = random.Random(seed)
    nD = nbad = nfix = 0
    examples = []
    for it in range(trials):
        n = rng.choice([8, 9, 10])
        r = one_even(n, rng.uniform(0.25, 0.45), rng)
        if r is None: continue
        K, z0 = r
        P = msl.far_pairs(K, rng)
        cls = {v: {v} for v in K}
        for a, b in P: cls[a] = {a, b}; cls[b] = {a, b}
        for u in sorted(K[z0]):
            K1 = msl.copy(K); K1[z0].discard(u); K1[u].discard(z0)
            z = z0
            W = cls[u]
            Ds = msl.all_decomps(K1, msl.lovasz_profile(K1), limit=20000, pairs=P)
            for D in Ds:
                iz = next(i for i, Q in enumerate(D) if Q[0] == z or Q[-1] == z)
                Q = D[iz] if D[iz][0] == z else D[iz][::-1]
                hit = [j for j, v in enumerate(Q) if v in W]
                if not hit: continue
                nD += 1
                m = hit[0]
                fixed = False
                for j in range(1, m):
                    v = Q[j]
                    k = next(k for k, R in enumerate(D) if k != iz and (R[0] == v or R[-1] == v))
                    R = D[k] if D[k][-1] == v else D[k][::-1]
                    A, B = Q[:j + 1], Q[j:]
                    if set(R) & set(B[1:]): continue
                    new = R + B[1:]
                    D2 = [X for t, X in enumerate(D) if t not in (iz, k)] + [A, new]
                    if msl.separates(D2, P):
                        fixed = True; break
                if fixed: nfix += 1
                else:
                    nbad += 1
                    if len(examples) < 3: examples.append((z, u, {v: sorted(K1[v]) for v in K1}, P, D))
    print("bad D' (Q_z meets [u]):", nD, "fixable by one option-1 swap:", nfix, "not:", nbad)
    for e in examples: print("  ex", e)
main(int(sys.argv[1]), int(sys.argv[2]))

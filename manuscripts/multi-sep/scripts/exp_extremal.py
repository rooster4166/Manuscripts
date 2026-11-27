"""Among separating Lovasz decompositions D' of K' = K - uz (u even in K'), does an extremal one
(minimising |V(Q_z)|, or the number of edges of Q_z) have Q_z avoiding [u]?  Small instances,
full enumeration."""
import random, sys
import msl
from exp_ee import one_even

def main(trials, seed):
    rng = random.Random(seed)
    tot = ok_any = ok_min = 0
    bad = []
    for it in range(trials):
        n = rng.choice([8, 9, 10])
        r = one_even(n, rng.uniform(0.25, 0.45), rng)
        if r is None: continue
        K, z = r
        P = msl.far_pairs(K, rng)
        cls = {v: {v} for v in K}
        for a, b in P: cls[a] = {a, b}; cls[b] = {a, b}
        for u in sorted(K[z]):
            K1 = msl.copy(K); K1[z].discard(u); K1[u].discard(z)
            Ds = msl.all_decomps(K1, msl.lovasz_profile(K1), limit=50000, pairs=P)
            if not Ds: continue
            def Qz(D):
                for Q in D:
                    if Q[0] == z or Q[-1] == z: return Q
            good = [D for D in Ds if not (set(Qz(D)) & cls[u])]
            tot += 1
            if good: ok_any += 1
            m = min(len(Qz(D)) for D in Ds)
            mins = [D for D in Ds if len(Qz(D)) == m]
            if all(not (set(Qz(D)) & cls[u]) for D in mins): ok_min += 1
            elif len(bad) < 3: bad.append((z, u, {v: sorted(K[v]) for v in K}, P, m))
    print("total", tot, "some D' good", ok_any, "all minimisers of |Q_z| good", ok_min)
    for b in bad: print("  min-fails", b)
if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]))

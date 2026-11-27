"""E-exp1: Case I of Lovasz's induction with many pairs.
K has one even vertex z; pairs at distance >= 3 (as many as possible).  For each u in N(z),
enumerate separating Lovasz decompositions D' of K - uz, and all Fan transfers z -> u.
Report per instance: A = some (u, D', chain) separates; B = some u such that every separating D'
has a separating transfer; C = for every u and every D' some chain works."""
import random, sys
import msl

def caseI_stats(K, z, pairs, limit=20000):
    res = {}
    for u in sorted(K[z]):
        K1 = msl.copy(K); K1[z].discard(u); K1[u].discard(z)
        b1 = msl.lovasz_profile(K1)
        Ds = msl.all_decomps(K1, b1, limit=limit, pairs=pairs)
        good = 0
        for D in Ds:
            ok = False
            for ch in msl.fan_chains(D, z, u, K1):
                D2 = msl.fan_exec(D, ch, u)
                assert msl.is_decomp(K, D2, msl.lovasz_profile(K)), (D, ch, D2)
                if msl.separates(D2, pairs):
                    ok = True; break
            good += ok
        res[u] = (good, len(Ds))
    return res

def main():
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    trials = int(sys.argv[1])
    tot = A = B = C = 0
    for it in range(trials):
        n = rng.choice([9, 11, 13])
        K = msl.random_odd_graph(n - 1, rng.uniform(0.2, 0.4), rng)
        if K is None: continue
        # make one even vertex: add new vertex z adjacent to an even number of vertices? Instead
        # remove an edge ux and hang a leaf at u (Case II construction)
        xs = [x for x in K if len(K[x]) >= 3]
        if not xs: continue
        x = rng.choice(xs); u = rng.choice(sorted(K[x]))
        K[x].discard(u); K[u].discard(x)
        l = n - 1; K[l] = {u}; K[u].add(l)
        z = x
        pairs = msl.far_pairs({v: K[v] for v in K if v != l} if False else K, rng)
        # only pairs not involving the leaf l
        pairs = [p for p in pairs if l not in p]
        if any(w not in {v for p in pairs for v in p} for w in K[z]):
            continue  # want all neighbours of z paired
        st = caseI_stats(K, z, pairs)
        if any(v[1] == 0 for v in st.values()):
            print("no separating D' for some u", st)
        tot += 1
        a = any(g > 0 for g, t in st.values())
        bb = any(g == t and t > 0 for g, t in st.values())
        c = all(g == t for g, t in st.values())
        A += a; B += bb; C += c
        if not bb:
            print("inst", n, "z", z, "pairs", pairs, "stats", st, "A" if a else "notA", flush=True)
            print("   K", {v: sorted(K[v]) for v in K})
    print("total", tot, "A", A, "B", B, "C", C)

main()

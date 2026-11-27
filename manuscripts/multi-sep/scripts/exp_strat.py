"""How often can Case I be handled by
  (Ia) a neighbour u of z with singleton class, or
  (Ib) a neighbour u of z such that [u] u [z] is a distance-3 set of K - uz ?
Instances: H = K - ux + u l (Case II output, l joins [x]) for cubic K with perfect pairings or
square colourings; and recursively the graphs met by a greedy strategy."""
import random, sys, subprocess
import msl
from g6 import g6_to_adj

def classes_ok(K, cls):
    for C in cls:
        for a in C:
            d = msl.dist(K, a)
            for b in C:
                if b != a and d.get(b, 99) < 3:
                    return False
    return True

def caseI_options(K, z, cl):
    """cl: dict v -> class id.  Returns list of (u, kind)."""
    members = {}
    for v, c in cl.items(): members.setdefault(c, set()).add(v)
    opts = []
    for u in K[z]:
        if len(members[cl[u]]) == 1:
            opts.append((u, 'Ia')); continue
        K1 = msl.copy(K); K1[z].discard(u); K1[u].discard(z)
        M = members[cl[u]] | members[cl[z]]
        ok = True
        for a in M:
            d = msl.dist(K1, a)
            for b in M:
                if b != a and d.get(b, 99) < 3: ok = False; break
            if not ok: break
        if ok: opts.append((u, 'Ib'))
    return opts

def main(n, ngraphs, seed, mode):
    rng = random.Random(seed)
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {n}", shell=True, capture_output=True, text=True).stdout.split()
    rng.shuffle(gs)
    tot = stuck = 0
    for s in gs[:ngraphs]:
        K = g6_to_adj(s)
        P = msl.far_pairs(K, rng, perfect_only=True)
        if P is None: continue
        cl = {}
        for i, (a, b) in enumerate(P): cl[a] = i; cl[b] = i
        # Case II
        x = rng.choice(sorted(K)); u = rng.choice(sorted(K[x]))
        H = msl.copy(K); H[x].discard(u); H[u].discard(x)
        l = n; H[l] = {u}; H[u].add(l); cl[l] = cl[x]
        o = caseI_options(H, x, cl)
        tot += 1
        if not o: stuck += 1
    print(f"n={n}: Case I at the Case II vertex: total {tot}, stuck {stuck}")

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] if len(sys.argv) > 4 else 'pair')

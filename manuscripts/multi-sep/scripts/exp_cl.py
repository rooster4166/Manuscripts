"""CL in genuine Case I configurations.  K0 cubic with a perfect pairing (classes of size 2).
Case II: H = K0 - ux + u l, l joins [x].  Case I at x: K' = H - xw for w in N_H(x): w is the
unique even vertex of K', x is odd.  Question CL: is there a rainbow Lovasz decomposition of K'
with Q_x avoiding [w]?  (Then appending xw gives a rainbow decomposition of H.)
Also report: does SOME w in N_H(x) work?"""
import random, sys, subprocess
import msl, oracle
from g6 import g6_to_adj

def main(n, ngraphs, per, seed, budget):
    rng = random.Random(seed)
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {n}", shell=True, capture_output=True, text=True).stdout.split()
    rng.shuffle(gs)
    tot = fail_w = fail_all = unk = 0
    for s in gs[:ngraphs]:
        K0 = g6_to_adj(s)
        for _ in range(per):
            P = msl.far_pairs(K0, rng, perfect_only=True)
            if P is None: continue
            cls = {}
            for a, b in P: cls[a] = {a, b}; cls[b] = cls[a]
            x = rng.choice(sorted(K0)); u = rng.choice(sorted(K0[x]))
            H = msl.copy(K0); H[x].discard(u); H[u].discard(x)
            l = n; H[l] = {u}; H[u].add(l)
            cls[x] = cls[x] | {l}; cls[l] = cls[x]
            for v in cls[x]: cls[v] = cls[x]
            sep = sorted({(a, b) for v in cls for a in cls[v] for b in cls[v] if a < b})
            okany = False
            for w in sorted(H[x]):
                K1 = msl.copy(H); K1[x].discard(w); K1[w].discard(x)
                avoid = {x: cls[w]}
                res = oracle.query("ASB", K1, msl.lovasz_profile(K1), sep=sep, avoid=avoid, seed=rng.randrange(1000), budget=budget)
                tot += 1
                if res == 0: fail_w += 1
                elif res == 2: unk += 1
                else: okany = True
            if not okany: fail_all += 1; print("NO w WORKS", s, P, x, u, flush=True)
    print(f"n={n}: (instance,w) total {tot} CL-fail {fail_w} unknown {unk}; instances with no good w: {fail_all}")
main(*map(int, sys.argv[1:6]))

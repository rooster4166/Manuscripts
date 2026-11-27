"""ELOV: if the vertices of positive even degree are pairwise at distance >= 3, is there a path
decomposition with b = deg mod 2 (no ends at even vertices, one at odd ones)?  Optionally with
classes (CSEP-E): even vertices form one extra class, or are spread over classes."""
import random, sys
import msl, oracle

def make(n, p, k, rng):
    """random graph whose even vertices are exactly a set S of k vertices pairwise at distance >= 3."""
    for _ in range(500):
        K = {v: set() for v in range(n)}
        for a in range(n):
            for b in range(a + 1, n):
                if rng.random() < p: K[a].add(b); K[b].add(a)
        V = list(K); rng.shuffle(V)
        S = []
        for v in V:
            if len(S) == k: break
            if all(msl.dist(K, v).get(s, 99) >= 3 for s in S): S.append(v)
        if len(S) < k: continue
        W = [v for v in K if (len(K[v]) % 2 == 0) != (v in S)]
        rng.shuffle(W)
        if len(W) % 2: continue
        while W:
            a, b = W.pop(), W.pop()
            if b in K[a]: K[a].discard(b); K[b].discard(a)
            else: K[a].add(b); K[b].add(a)
        if any(not K[v] for v in K): continue
        ev = [v for v in K if len(K[v]) % 2 == 0]
        if sorted(ev) != sorted(S): continue
        if all(msl.dist(K, a).get(b, 99) >= 3 for a in S for b in S if a != b):
            return K, S
    return None

def main(trials, seed, budget):
    rng = random.Random(seed)
    tot = fail = unk = 0
    for it in range(trials):
        n = rng.choice([8, 10, 12, 14])
        k = rng.choice([2, 3, 4])
        r = make(n, rng.uniform(0.15, 0.4), k, rng)
        if r is None: continue
        K, S = r
        res = oracle.query("PB", K, msl.lovasz_profile(K), seed=rng.randrange(1000), budget=budget)
        tot += 1
        if res == 0:
            fail += 1
            if fail <= 3: print("FAIL", S, {v: sorted(K[v]) for v in K}, flush=True)
        elif res == 2: unk += 1
    print(f"ELOV: total {tot} fail {fail} unknown {unk}")
main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))

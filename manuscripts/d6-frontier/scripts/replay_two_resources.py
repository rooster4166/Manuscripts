"""Replay of the two-resource root-hub certificate (Theorem 5 of d6-frontier.tex).

d = 6, U = {0..5} induces K6, r = 0.  Pendant y (any number of T-neighbours), battery
triangle r a b with |N(a) & T| <= 4, y adjacent to neither a nor b, and
|N(y) & N(a) & T| <= 2; d(r) >= 10.  This is the residual regime of Theorem 4(i): here
y and a may both have three or more T-neighbours.  Seed: hold star(r,T), ry, ra, rb, ab;
even vertices r, y; Lemma-3 partition b(r) = 2, b(y) = 0 (CP-SAT)."""
import sys, random
sys.path.insert(0, '/home/user/Manuscripts/tools')
from pathnum2 import decompose
from fan_engine import fan_add, ends, verify, blank_nbrs
from gen import build

def one(seed, n):
    rng = random.Random(seed)
    U = list(range(6)); r = 0; T = U[1:]
    y, a, b = 6, 7, 8
    Na = set(rng.sample(T, rng.randint(3, 4)))
    C = set(rng.sample(sorted(Na), rng.randint(0, 2)))
    Ny = C | set(t for t in T if t not in Na and rng.random() < 0.7)
    req = [(r, y), (r, a), (r, b), (a, b), (r, 9), (r, 10)] + [(a, t) for t in Na] + [(y, t) for t in Ny]
    forb = [(a, t) for t in T if t not in Na] + [(y, t) for t in T if t not in Ny] + [(y, a), (y, b)]
    G = build(n, req, forb, rng)
    if G is None or G.degree(r) < 10: return None
    k = n // 2
    held = [(r, t) for t in T] + [(r, y), (r, a), (r, b), (a, b)]
    G0 = G.copy(); G0.remove_edges_from(held)
    assert sorted(v for v in G0 if G0.degree(v) % 2 == 0) == [r, y]
    ex = {v: 1 for v in G0 if G0.degree(v) % 2}; ex[r] = 2; ex[y] = 0
    st, D = decompose(G0, k, exact_ends=ex, time_limit=300, workers=2); assert D is not None, st
    V = list(G); log = []
    def step(recv, donors, bound):
        nonlocal D
        bl = blank_nbrs(D, V, recv); sup = sum(ends(D, V)[t] for t in donors)
        assert bl <= bound < sup, (recv, donors, bl, bound, sup)
        log.append((sup, bl)); D, t = fan_add(D, recv, donors); return t
    step(r, [b], 0); step(b, [a], 0)                         # carry: a parked
    z1 = next(t for t in T if t not in Na)
    Z = [step(r, [z1], 0)]
    Cy = sorted(set(G[y]) & set(G[a]) & set(T))
    P2 = Cy if len(Cy) == 2 else [t for t in T if t not in Z]
    Z.append(step(r, P2, 1))
    Z.append(step(r, [t for t in T if t not in Z], 2))
    S = [t for t in T if t not in Z]
    adj = lambda s: (s in G[y]) + (s in G[a])
    S.sort(key=lambda s: -adj(s))
    step(S[0], [r], 5); step(S[1], [r], 4)
    step(y, [r], 3); step(a, [r], 2)
    assert verify(D, G) and len(D) == k
    bb = ends(D, V); assert bb[r] == 2 and all(bb[v] == 1 for v in G if G.degree(v) % 2)
    return len(Na), len(Ny), log

if __name__ == '__main__':
    s0, N, n = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    done = 0; s = s0
    while done < N:
        res = one(s, n); s += 1
        if res is None: continue
        done += 1; print("seed", s - 1, "n", n, "|N(a)&T|", res[0], "|N(y)&T|", res[1], "(supply, blanks):", res[2], flush=True)
    print("two-resource replay: all", done, "instances verified")

"""Replay of the distant-pendant root-hub certificate (Theorem 6 of d6-frontier.tex).

Hypotheses (d = 6): U = {0..5} induces K6, r = 0, d(r) >= 8; a path r c_1 ... c_m a of odd
vertices with |N(c_1) & T| <= 4, c_2..c_m and a without neighbours in U, a not adjacent to
r, d(a) >= 3.  Seed: hold star(r,T) and the path; the even vertices of the seed are r, a;
partition with b(r) = 2, b(a) = 0 (endpoint-structure Lemma 3), found by CP-SAT.
Transfers: z1 -> r (z1 a T-vertex missed by c_1), two grouped receipts at r, r -> s1,
r -> s2, then the relay r -> c_1 -> ... -> c_m -> a."""
import sys, random
sys.path.insert(0, '/home/user/Manuscripts/tools')
from pathnum2 import decompose
from fan_engine import fan_add, ends, verify, blank_nbrs
from gen import build

def one(seed, n, m):
    rng = random.Random(seed)
    U = list(range(6)); r = 0; T = U[1:]
    cs = list(range(6, 6 + m)); a = 6 + m
    c1 = cs[0]
    k1 = rng.randint(3, 4)                       # |N(c_1) & T|: 3 or 4 (residual-type)
    Nc1 = set(rng.sample(T, k1))
    path = [r] + cs + [a]
    required = list(zip(path, path[1:])) + [(c1, t) for t in Nc1] + [(r, 6 + m + 1), (r, 6 + m + 2)]
    forbidden = [(c1, t) for t in T if t not in Nc1] + [(v, u) for v in cs[1:] + [a] for u in U] + [(a, r)] + [(a, c) for c in cs[:-1]]
    G = build(n, required, forbidden, rng)
    if G is None or G.degree(r) < 8 or G.degree(a) < 3: return None
    k = n // 2
    held = [(r, t) for t in T] + list(zip(path, path[1:]))
    G0 = G.copy(); G0.remove_edges_from(held)
    ev = [v for v in G0 if G0.degree(v) % 2 == 0]
    assert sorted(ev) == sorted([r, a]), ev
    ex = {v: 1 for v in G0 if G0.degree(v) % 2}; ex[r] = 2; ex[a] = 0
    st, D = decompose(G0, k, exact_ends=ex, time_limit=300, workers=2)
    assert D is not None, st
    V = list(G); log = []
    def step(recv, donors, bound):
        nonlocal D
        bl = blank_nbrs(D, V, recv); sup = sum(ends(D, V)[t] for t in donors)
        assert bl <= bound < sup, (recv, donors, bl, bound, sup)
        log.append((sup, bl))
        D, t = fan_add(D, recv, donors); return t
    z1 = next(t for t in T if t not in Nc1)
    Z = [step(r, [z1], 0)]
    for j in (1, 2):
        Z.append(step(r, [t for t in T if t not in Z], j))
    for s in [t for t in T if t not in Z]:
        step(s, [r], 3)
    step(c1, [r], 2)                              # first relay: |N(c1) & Z| <= 2
    for prev, nxt in zip(cs, cs[1:] + [a]):
        step(nxt, [prev], 0)                      # quiet relays and the parked vertex
    assert verify(D, G) and len(D) == k
    b = ends(D, V); assert b[r] == 2 and all(b[v] == 1 for v in G if G.degree(v) % 2)
    return log

if __name__ == '__main__':
    s0, N, n, m = map(int, sys.argv[1:5])
    done = 0; s = s0
    while done < N:
        res = one(s, n, m); s += 1
        if res is None: continue
        done += 1; print("seed", s - 1, "n", n, "m", m, "(supply, blanks):", res, flush=True)
    print("relay replay: all", done, "instances verified")

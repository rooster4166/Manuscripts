"""Replay of the root-hub battery certificates for non-universal roots (Theorem 4(ii),(iii)
of d6-frontier.tex): core shapes D = K2 with r on the missing edge (|Q| = 1), and
D in {P3 (r the middle vertex), K3 (r a triangle vertex), C4 (r a cycle vertex)} (|Q| = 2),
where Q = T - N(r).  Battery: triangle r a b of odd vertices; |Q| = 1: |N(a) & T| <= 2 and
b not adjacent to q;  |Q| = 2: |N(a) & N_T(r)| <= 1 and b not adjacent to q2.
Seed: hold star(r, N_T(r)) and the triangle; the even vertices of the seed are r, q
(|Q| = 1) or q1, q2 (|Q| = 2); Lemma-3 partition doubling r (resp. q1) via CP-SAT."""
import sys, random
sys.path.insert(0, '/home/user/Manuscripts/tools')
from pathnum2 import decompose
from fan_engine import fan_add, ends, verify, blank_nbrs
from gen import build

SHAPES = {   # missing core edges, with r = 0
    'K2': [(0, 1)],
    'P3': [(1, 0), (0, 2)],
    'K3': [(0, 1), (0, 2), (1, 2)],
    'C4': [(0, 1), (1, 3), (3, 2), (2, 0)],
}

def one(seed, n, shape):
    rng = random.Random(seed)
    U = list(range(6)); r = 0; T = U[1:]
    miss = SHAPES[shape]
    NT = [t for t in T if (r, t) not in miss and (t, r) not in miss]
    Q = [t for t in T if t not in NT]
    a, b = 6, 7
    if len(Q) == 1:
        Na = set(rng.sample(T, rng.randint(0, 2)))
        forb = [(a, t) for t in T if t not in Na] + [(b, Q[0])]
    else:
        Na = set(rng.sample(NT, rng.randint(0, 1))) | set(q for q in Q if rng.random() < 0.5)
        forb = [(a, t) for t in T if t not in Na] + [(b, Q[1])]
    req = [(r, a), (r, b), (a, b)] + [(a, t) for t in Na] + [(r, 8), (r, 9)]
    G = build(n, req, forb, rng, core_missing=miss)
    if G is None or G.degree(r) < 8: return None
    k = n // 2
    held = [(r, t) for t in NT] + [(r, a), (r, b), (a, b)]
    G0 = G.copy(); G0.remove_edges_from(held)
    ev = sorted(v for v in G0 if G0.degree(v) % 2 == 0)
    want_ev = sorted([r] + Q) if len(Q) == 1 else sorted(Q)
    assert ev == want_ev, (ev, want_ev)
    ex = {v: 1 for v in G0 if G0.degree(v) % 2}
    if len(Q) == 1: ex[r] = 2; ex[Q[0]] = 0
    else: ex[Q[0]] = 2; ex[Q[1]] = 0
    st, D = decompose(G0, k, exact_ends=ex, time_limit=300, workers=2); assert D is not None, st
    V = list(G); log = []
    def step(recv, donors, bound):
        nonlocal D
        bl = blank_nbrs(D, V, recv); sup = sum(ends(D, V)[t] for t in donors)
        assert bl <= bound < sup, (recv, donors, bl, bound, sup)
        log.append((sup, bl)); D, t = fan_add(D, recv, donors); return t
    step(r, [b], 0); step(b, [a], 0)                     # battery carry: a parked
    first = [t for t in NT if t in Na] or NT
    Z = [step(r, [first[0]], 0)]
    Z.append(step(r, [t for t in NT if t not in Z], 1))
    S = [t for t in NT if t not in Z]
    S.sort(key=lambda s: s not in Na)
    sup = ends(D, V)[r]
    for s in S:
        step(s, [r], 3); 
    step(a, [r], 2)
    assert verify(D, G) and len(D) == k
    bb = ends(D, V); assert bb[r] == 2 and all(bb[v] == 1 for v in G if G.degree(v) % 2)
    return log

if __name__ == '__main__':
    shape, s0, N, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    done = 0; s = s0
    while done < N:
        res = one(s, n, shape); s += 1
        if res is None: continue
        done += 1; print(shape, "seed", s - 1, "n", n, "(supply, blanks):", res, flush=True)
    print("shape", shape, "root-hub battery replay: all", done, "instances verified")

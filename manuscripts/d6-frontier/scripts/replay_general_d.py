"""Replay of the general-d hub certificates (Theorems 7 and 8 of d6-frontier.tex) at
deletion degree d = 8 (eight even vertices inducing K8), and d = 6 for comparison.

root  : C-universal root r = 0 with a quiet pendant y and beta = d/2 - 3 quiet battery
        triangles r a_i b_i  (Lemma-3 seed: even vertices r, y; b(r) = 2, b(y) = 0).
full  : x adjacent to all of U with beta = d/2 - 1 quiet battery triangles x a_i b_i
        (Lovasz seed: all odd), every root r checked."""
import sys, random
sys.path.insert(0, '/home/user/Manuscripts/tools')
from pathnum2 import decompose
from fan_engine import fan_add, ends, verify, blank_nbrs
from gen import build

def run_schedule(G, D, V, plan):
    for recv, donors, bound in plan(D):
        pass

def root_case(seed, n, d):
    rng = random.Random(seed)
    U = list(range(d)); r = 0; T = U[1:]
    beta = d // 2 - 3
    y = d; bat = [(d + 1 + 2 * i, d + 2 + 2 * i) for i in range(beta)]   # (a_i, b_i)
    req = [(r, y)] + [e for a, b in bat for e in ((r, a), (r, b), (a, b))]
    forb = [(v, u) for v in [y] + [a for a, _ in bat] for u in T]
    forb += [(b, y) for _, b in bat] + [(bat[i][0], bat[j][1]) for i in range(beta) for j in range(i + 1, beta)]
    G = build(n, req, forb, rng, d=d)
    if G is None or G.degree(r) < d + 2 + 2 * beta or G.degree(y) < 3: return None
    k = n // 2
    held = [(r, t) for t in T] + [(r, y)] + [e for a, b in bat for e in ((r, a), (r, b), (a, b))]
    G0 = G.copy(); G0.remove_edges_from(held)
    ev = sorted(v for v in G0 if G0.degree(v) % 2 == 0); assert ev == [r, y], ev
    ex = {v: 1 for v in G0 if G0.degree(v) % 2}; ex[r] = 2; ex[y] = 0
    st, D = decompose(G0, k, exact_ends=ex, time_limit=600, workers=2); assert D is not None, st
    V = list(G); log = []
    def step(recv, donors, bound):
        nonlocal D
        bl = blank_nbrs(D, V, recv); sup = sum(ends(D, V)[t] for t in donors)
        assert bl <= bound < sup, (recv, donors, bl, bound, sup)
        log.append((sup, bl)); D, t = fan_add(D, recv, donors); return t
    for a, b in bat:
        step(r, [b], 0); step(b, [a], 0)
    Z = []
    for j in range(d // 2):
        Z.append(step(r, [t for t in T if t not in Z], j))
    for s in [t for t in T if t not in Z]:
        step(s, [r], d // 2)
    step(y, [r], beta)
    for i, (a, b) in enumerate(bat):
        step(a, [r], beta - 1 - i)
    assert verify(D, G) and len(D) == k
    b = ends(D, V); assert b[r] == 2 and all(b[v] == 1 for v in G if G.degree(v) % 2)
    return log

def full_case(seed, n, d):
    rng = random.Random(seed)
    U = list(range(d)); x = d; beta = d // 2 - 1
    bat = [(d + 1 + 2 * i, d + 2 + 2 * i) for i in range(beta)]
    req = [(x, u) for u in U] + [e for a, b in bat for e in ((x, a), (x, b), (a, b))]
    forb = [(a, u) for a, _ in bat for u in U] + [(bat[i][0], bat[j][1]) for i in range(beta) for j in range(i + 1, beta)]
    G = build(n, req, forb, rng, d=d)
    if G is None: return None
    k = n // 2
    held = [(x, u) for u in U] + [e for a, b in bat for e in ((x, a), (x, b), (a, b))]
    G0 = G.copy(); G0.remove_edges_from(held)
    assert all(G0.degree(v) % 2 for v in G0)
    st, D0 = decompose(G0, k, exact_ends={v: 1 for v in G0}, time_limit=600, workers=2); assert D0 is not None, st
    V = list(G); logs = []
    for r in U:
        D = list(D0); log = []
        def step(recv, donors, bound):
            nonlocal D
            bl = blank_nbrs(D, V, recv); sup = sum(ends(D, V)[t] for t in donors)
            assert bl <= bound < sup, (recv, donors, bl, bound, sup)
            log.append((sup, bl)); D, t = fan_add(D, recv, donors); return t
        for a, b in bat:
            step(x, [b], 0); step(b, [a], 0)
        T = [u for u in U if u != r]; Z = []
        for j in range(d // 2):
            Z.append(step(x, [t for t in T if t not in Z], j))
        for u in [r] + [t for t in T if t not in Z]:
            step(u, [x], d // 2)
        for i, (a, b) in enumerate(bat):
            step(a, [x], beta - 1 - i)
        assert verify(D, G) and len(D) == k
        bb = ends(D, V); assert bb[r] == 2 and all(bb[v] == 1 for v in G if G.degree(v) % 2)
        logs.append(log)
    return logs[0]

if __name__ == '__main__':
    kind, s0, N, n, d = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    f = root_case if kind == 'root' else full_case
    done = 0; s = s0
    while done < N:
        res = f(s, n, d); s += 1
        if res is None: continue
        done += 1; print(kind, "d", d, "seed", s - 1, "n", n, "(supply, blanks):", res, flush=True)
    print(kind, "hub replay at d =", d, ": all", done, "instances verified")

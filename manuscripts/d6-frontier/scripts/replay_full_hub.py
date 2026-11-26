"""Replay of the full-hub battery certificate (Theorem 6 of d6-frontier.tex).

Hypotheses: U = {0..5} = even vertices (here inducing K6), x = 6 adjacent to all of U,
batteries: triangles x a1 b1, x a2 b2 (a_i = 7, 9; b_i = 8, 10) with N(a_i) & U empty and
a1 b2 not an edge.  Seed: G0 = G - star(x, U) - both triangles is all-odd; an exact
one-end-per-vertex partition (Lovasz) is obtained by CP-SAT.  The twelve transfers of the
proof are executed with fan_engine for EVERY root r in U, checking each inequality."""
import sys, random
sys.path.insert(0, '/home/user/Manuscripts/tools')
from pathnum2 import decompose
from fan_engine import fan_add, ends, verify, blank_nbrs
from gen import build

def one(seed, n):
    rng = random.Random(seed)
    U = list(range(6)); x, a1, b1, a2, b2 = 6, 7, 8, 9, 10
    required = [(x, u) for u in U] + [(x, a1), (x, b1), (a1, b1), (x, a2), (x, b2), (a2, b2)]
    forbidden = [(a, u) for a in (a1, a2) for u in U] + [(a1, b2)]
    G = build(n, required, forbidden, rng)
    if G is None: return None
    k = n // 2
    held = [(x, u) for u in U] + [(x, a1), (x, b1), (a1, b1), (x, a2), (x, b2), (a2, b2)]
    G0 = G.copy(); G0.remove_edges_from(held)
    assert all(G0.degree(v) % 2 == 1 for v in G0)
    st, D0 = decompose(G0, k, exact_ends={v: 1 for v in G0}, time_limit=300, workers=2)
    assert D0 is not None, st
    V = list(G); out = []
    for r in U:
        D = list(D0)
        def step(recv, donors, bound):
            nonlocal D
            bl = blank_nbrs(D, V, recv)
            sup = sum(ends(D, V)[t] for t in donors)
            assert bl <= bound < sup, (recv, donors, bl, bound, sup)
            D, t = fan_add(D, recv, donors)
            return t, (sup, bl)
        step(x, [b1], 0); step(b1, [a1], 0)          # battery 1: x gains, a1 parked
        step(x, [b2], 0); step(b2, [a2], 0)          # battery 2: x gains, a2 parked
        T = [u for u in U if u != r]; Z = []
        for j in range(3):                           # receipts at x from T
            z, _ = step(x, [t for t in T if t not in Z], j); Z.append(z)
        assert ends(D, V)[x] == 6
        log = []
        for u in [r] + [t for t in T if t not in Z]:  # donations x -> r, s1, s2
            _, sb = step(u, [x], 3); log.append(sb)
        _, sb = step(a1, [x], 1); log.append(sb)      # paybacks
        _, sb = step(a2, [x], 0); log.append(sb)
        assert verify(D, G) and len(D) == k
        b = ends(D, V)
        assert b[r] == 2 and all(b[v] == 1 for v in G if G.degree(v) % 2)
        out.append((r, log))
    return out

if __name__ == '__main__':
    s0, N, n = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    done = 0; s = s0
    while done < N:
        res = one(s, n); s += 1
        if res is None: continue
        done += 1
        print("seed", s - 1, "n", n, "roots verified:", [r for r, _ in res], "sample (supply, blanks):", res[0][1], flush=True)
    print("full-hub replay: all", done, "instances verified at every root")

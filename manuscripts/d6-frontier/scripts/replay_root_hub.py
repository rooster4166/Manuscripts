"""Replay of the root-hub certificate (Theorem 4 of d6-frontier.tex) on random graphs.

Hypotheses: G has even order, its six even vertices U = {0..5} induce K6 (so the root
r = 0 is adjacent to all of T = U - r), d(r) >= 8, and r has an odd neighbour y with
|N(y) & T| <= 2 and d(y) >= 3.  Seed: G0 = G - {rt : t in T} - ry, whose even vertices
are r, y; a partition of G0 with b(r) = 2, b(y) = 0, b = 1 elsewhere (Lemma 3 of the
endpoint-structure note) is obtained by CP-SAT.  Then the six transfers of the proof are
executed with fan_engine and every inequality used in the proof is checked."""
import sys, random
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from pathnum2 import decompose
from fan_engine import fan_add, ends, verify, blank_nbrs
from gen import build

FORCE_C = None

def one(seed, n):
    rng = random.Random(seed)
    U = list(range(6)); r = 0; T = U[1:]
    y = 6
    c = FORCE_C if FORCE_C is not None else rng.randint(0, 2)
    Ny = set(rng.sample(T, c))
    required = [(r, y)] + [(y, t) for t in Ny]
    forbidden = [(y, t) for t in T if t not in Ny]
    # make some exterior vertices full, to stay inside the residual class of Q2
    fulls = [7, 8] if n >= 12 else [7]
    required += [(f, u) for f in fulls for u in U]
    G = build(n, required, forbidden, rng)
    if G is None or G.degree(r) < 8 or G.degree(y) < 3:
        return None
    k = n // 2
    G0 = G.copy(); G0.remove_edges_from([(r, t) for t in T] + [(r, y)])
    ex = {v: 1 for v in G0 if G0.degree(v) % 2}
    ex[r] = 2; ex[y] = 0
    st, D = decompose(G0, k, exact_ends=ex, time_limit=300, workers=2)
    assert D is not None, ("seed missing", st)
    V = list(G)
    log = []
    p = sorted(Ny)[0] if Ny else T[0]
    # S1: single transfer p -> r
    assert ends(D, V)[p] > blank_nbrs(D, V, r) == 0
    D, t = fan_add(D, r, [p]); assert t == p
    # S2, S3: grouped transfers into r
    for need in (1, 2):
        donors = [t for t in T if ends(D, V)[t] == 1 and not any(r in P and t in P and abs(P.index(r) - P.index(t)) == 1 for P in D)]
        bl = blank_nbrs(D, V, r)
        assert bl == need and sum(ends(D, V)[t] for t in donors) > bl, (bl, donors)
        D, t = fan_add(D, r, donors)
    b = ends(D, V)
    Z = [t for t in T if b[t] == 0]; S = [t for t in T if b[t] == 1]
    assert len(Z) == 3 and len(S) == 2 and b[r] == 5 and p in Z
    S.sort(key=lambda s: s not in Ny)          # the receiver adjacent to y (if any) first
    for s in S:
        bl = blank_nbrs(D, V, s)
        assert ends(D, V)[r] > bl, ("D-step", ends(D, V)[r], bl)
        log.append((ends(D, V)[r], bl))
        D, t = fan_add(D, s, [r])
    bl = blank_nbrs(D, V, y)
    assert ends(D, V)[r] == 3 > bl
    log.append((3, bl))
    D, t = fan_add(D, y, [r])
    assert verify(D, G) and len(D) == k
    b = ends(D, V)
    assert b[r] == 2 and all(b[v] == 1 for v in G if G.degree(v) % 2)
    return n, c, log

if __name__ == '__main__':
    s0, N, n = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    if len(sys.argv) > 4: FORCE_C = int(sys.argv[4])
    done = 0; s = s0
    while done < N:
        res = one(s, n); s += 1
        if res is None: continue
        done += 1
        print("seed", s - 1, "n", res[0], "|N(y)&T|", res[1], "(supply, blanks) at D-steps and payback:", res[2], flush=True)
    print("root-hub replay: all", done, "instances verified")

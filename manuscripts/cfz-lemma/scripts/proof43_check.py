"""Sanity check of the case analysis in the proof of Theorem 4 (common-vertex (4,3)).

The proof is run as an algorithm on random configurations.  Each branch builds
explicit paths; the black-box steps (Lemma 1 = path-cycle, Lemma 2 = sum <= 6,
Lemma 3 = six contacts) are checked with the exact oracle.  An AssertionError
would expose a gap in the case analysis.
"""
import random, sys, itertools
from decomp import paths_at_most
from moves43_stress import ham_instance, nested_instance

def nb(C, v):
    i = C.index(v); L = len(C); return [C[(i-1) % L], C[(i+1) % L]]

def cedges(C):
    return [(C[i], C[(i+1) % len(C)]) for i in range(len(C))]

def is_path_edges(vs):
    return len(set(vs)) == len(vs)

def opened(C, v, u):
    """C minus edge vu, as a vertex sequence from v to u."""
    i = C.index(v); L = len(C)
    if C[(i+1) % L] == u:
        seq = [C[(i - k) % L] for k in range(L)]
    else:
        assert C[(i-1) % L] == u
        seq = [C[(i + k) % L] for k in range(L)]
    assert seq[0] == v and seq[-1] == u
    return seq

def pe(seq):
    return [(seq[i], seq[i+1]) for i in range(len(seq)-1)]

def finish(paths, rest_edges, k):
    """paths are explicit; rest must split into k paths (black-box lemma)."""
    for p in paths: assert is_path_edges(p), p
    ok = paths_at_most(rest_edges, k)
    assert ok, ("black box failed", paths, rest_edges, k)
    return len(paths) + k

def prove(P, Cs):
    p1, p4 = P[0], P[-1]
    Pe = pe(P)
    # Step 1 (M1): a cycle missing an end
    for Pd in (P, P[::-1]):
        for i, C in enumerate(Cs):
            if Pd[0] in C: continue
            j = min(k for k in range(4) if Pd[k] in C)
            pj = Pd[j]
            ts = [t for t in nb(C, pj) if t not in Pd[j:]]
            assert ts, "M1 blocked"
            t = ts[0]
            Q = opened(C, pj, t)[::-1][:-1] + []  # t ... pj
            Q = opened(C, pj, t)
            Q = Q[::-1] + Pd[:j][::-1]            # t ...C... pj, then prefix back to Pd[0]
            # careful: opened gives pj..t ; reversed gives t..pj ; then append prefix reversed
            Q = opened(C, pj, t)[::-1]
            Q = Q + Pd[:j][::-1]
            assert is_path_edges(Q)
            Pp = [t] + Pd[j:]
            rest = pe(Pp) + [e for D in Cs if D is not C for e in cedges(D)]
            assert len(Pp) + 2 <= 6
            return 'M1', finish([Q], rest, 3)
    # Step 2: exchanges at p1
    for a, b in itertools.permutations(range(3), 2):
        A, B = Cs[a], Cs[b]
        us = [u for u in nb(A, p1) if u not in B]; ws = [w for w in nb(B, p1) if w not in A]
        if us and ws and a < b:
            Q1 = opened(A, p1, us[0])[::-1] + [ws[0]]
            Q2 = opened(B, p1, ws[0])[::-1] + [us[0]]
            k = 3 - a - b
            return 'exch', finish([Q1, Q2], Pe + cedges(Cs[k]), 2)
    arc = lambda i, j: any(u not in Cs[j] for u in nb(Cs[i], p1))
    for (i, j, k) in ((0, 1, 2), (0, 2, 1)):
        if arc(i, j) and arc(j, k) and arc(k, i):
            ui = [u for u in nb(Cs[i], p1) if u not in Cs[j]][0]
            uj = [u for u in nb(Cs[j], p1) if u not in Cs[k]][0]
            uk = [u for u in nb(Cs[k], p1) if u not in Cs[i]][0]
            Qs = [opened(Cs[j], p1, uj)[::-1] + [ui], opened(Cs[k], p1, uk)[::-1] + [uj],
                  opened(Cs[i], p1, ui)[::-1] + [uk]]
            return 'circ', finish(Qs, Pe, 1)
    srcs = [s for s in range(3) if not any(arc(i, s) for i in range(3) if i != s)]
    assert srcs, "no source"
    s = srcs[0]; S = Cs[s]
    assert len(set(S)) >= 7
    A, B = [Cs[i] for i in range(3) if i != s]
    def two_end(F, X, Y):
        for t in nb(X, p1):
            if t in P: continue
            for y in nb(Y, p4):
                if y in P or y == t: continue
                R = [t] + P + [y]
                if set(F) <= set(R): continue
                QX = opened(X, p1, t); QY = opened(Y, p4, y)
                return finish([QX, QY], pe(R) + cedges(F), 2)
        return None
    for F, X, Y, tag in ((S, A, B, 'opt1'), (S, B, A, 'opt2')):
        r = two_end(F, X, Y)
        if r: return tag, r
    # failure cases: the proof asserts that one of (F1), (F2), (F3) holds
    al = set(nb(A, p1)) - set(P); be = set(nb(B, p1)) - set(P)
    al4 = set(nb(A, p4)) - set(P); be4 = set(nb(B, p4)) - set(P)
    cross = lambda C: set(nb(C, p1)) == {P[2], P[3]} and set(nb(C, p4)) == {P[0], P[1]}
    if cross(A) or cross(B):
        Fc = A if cross(A) else B; Oc = B if Fc is A else A
        # (F1)/(F2): hold back the cross cycle, open the other one and S at the two ends
        for X, Y, tag in ((Oc, S, 'F1-a'), (S, Oc, 'F1-b')):
            r = two_end(Fc, X, Y)
            if r: return tag, r
        raise AssertionError(("F1 unresolved", P, Cs))
    assert len(al) == len(be) == len(al4) == len(be4) == 1 and al == be4 and be == al4, ("not F3", P, Cs)
    # (F3): F = the cycle containing p1p4, X = S at p1, Y = the other cycle at p4
    Fc = A if P[3] in nb(A, p1) else B; Oc = B if Fc is A else A
    v = (set(nb(Oc, p4)) - set(P)).pop()
    for t in nb(S, p1):
        assert t not in P and t != v
        R = [t] + P + [v]
        assert not set(Fc) <= set(R)
        return 'F3', finish([opened(S, p1, t), opened(Oc, p4, v)], pe(R) + cedges(Fc), 2)
    raise AssertionError(("unhandled", P, Cs))

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); T = int(sys.argv[2])
    stats = {}
    for _ in range(T):
        if rng.random() < 0.4:
            P, Cs = ham_instance(rng.choice([9, 11, 13]), rng)
        else:
            inst = nested_instance(rng.choice([7, 8, 9, 10, 12]), rng)
            if inst is None: continue
            P, Cs = inst
        tag, n = prove(P, Cs)
        assert n == 4
        stats[tag] = stats.get(tag, 0) + 1
    print(stats)

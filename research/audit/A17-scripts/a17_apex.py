#!/usr/bin/env python3
"""A17: Lemma 4.2 (apex finish) of manuscripts/near-dirac/near-dirac.tex.

Given a Hamilton decomposition C_1..C_{D/2} of the two-apex graph J (apices a1, a2
non-adjacent), the proof cuts every cycle at both apices, discards single-vertex
pieces (singular vertices, from a1 v a2), and splits a non-trivial piece of some
other cycle at each singular vertex. Claim: exactly D paths, b'(v) ends at every v,
edge sets partition E(R).

We cannot run CKLOT, so we build J synthetically as the union of D/2 cycles of a
Walecki decomposition of K_N under a random relabelling (excluding the cycle that
contains a1a2), so that J is D-regular, simple, a1a2 not an edge, and b'(v) is the
number of apex neighbours. We force instances with several singular vertices.
We also run the conversion on cycles that share a 'host' cycle for several
singular vertices (all choose the same j'), the case where splits interact.
"""
import random
import sys


def walecki(N):
    """Walecki Hamilton decomposition of K_N, N odd: (N-1)/2 cycles."""
    if N % 2 == 1:
        n = N - 1  # vertices 0..n-1 on a circle plus infinity = n
        cycles = []
        for i in range(n // 2):
            seq = [i]
            for k in range(1, n):
                step = (k + 1) // 2
                seq.append((i + step) % n if k % 2 == 1 else (i - step) % n)
            path = seq  # Hamilton path on 0..n-1
            cycles.append([n] + path)
        return cycles
    raise ValueError("odd N only")


def check_ham_decomp(N, cycles):
    seen = set()
    for C in cycles:
        assert sorted(C) == list(range(N))
        for a, b in zip(C, C[1:] + C[:1]):
            e = (min(a, b), max(a, b))
            assert e not in seen
            seen.add(e)
    return seen


def convert(cycles, a1, a2, rnd, host_mode='random'):
    """The proof of Lemma 4.2. Returns list of paths (vertex lists)."""
    pieces = []  # list of (j, path)
    singular = {}
    for j, C in enumerate(cycles):
        i1 = C.index(a1)
        Cr = C[i1:] + C[:i1]  # starts at a1
        i2 = Cr.index(a2)
        arc1 = Cr[1:i2]
        arc2 = Cr[i2 + 1:]
        assert arc1 and arc2, 'apices adjacent'
        for arc in (arc1, arc2):
            if len(arc) == 1:
                v = arc[0]
                assert v not in singular, 'singular twice'
                singular[v] = j
            else:
                pieces.append([j, arc])
    nD = len(cycles) * 2
    # split at each singular vertex in turn
    for v, jv in singular.items():
        others = [j for j in range(len(cycles)) if j != jv]
        if host_mode == 'same':
            jp = others[0]
        else:
            jp = rnd.choice(others)
        idx = [t for t, (j, P) in enumerate(pieces) if j == jp and v in P]
        assert len(idx) == 1
        t = idx[0]
        j, P = pieces[t]
        k = P.index(v)
        assert 0 < k < len(P) - 1, 'singular vertex is not interior in its host piece'
        pieces[t] = [j, P[:k + 1]]
        pieces.append([j, P[k:]])
    return [P for j, P in pieces], nD, singular


def trial(N, D, rnd, force_sing, host_mode):
    assert N % 2 == 1
    base = walecki(N)
    assert len(check_ham_decomp(N, base)) == N * (N - 1) // 2
    for _ in range(2000):
        perm = list(range(N))
        rnd.shuffle(perm)
        cyc = [[perm[v] for v in C] for C in base]
        a1, a2 = 0, 1
        good = [C for C in cyc if not any({x, y} == {a1, a2} for x, y in zip(C, C[1:] + C[:1]))]
        rnd.shuffle(good)
        chosen = good[:D // 2]
        # count singular
        ns = 0
        for C in chosen:
            i = C.index(a1)
            if C[(i + 2) % N] == a2 or C[(i - 2) % N] == a2:
                ns += 1
        if ns >= force_sing:
            break
    # J edges, R, b'
    JE = set()
    for C in chosen:
        for x, y in zip(C, C[1:] + C[:1]):
            e = (min(x, y), max(x, y))
            assert e not in JE
            JE.add(e)
    deg = {}
    for x, y in JE:
        deg[x] = deg.get(x, 0) + 1
        deg[y] = deg.get(y, 0) + 1
    assert all(d == D for d in deg.values()) and len(deg) == N
    assert (min(a1, a2), max(a1, a2)) not in JE
    R = set(e for e in JE if a1 not in e and a2 not in e)
    bp = {v: 0 for v in range(N) if v not in (a1, a2)}
    for x, y in JE:
        for (ap, o) in ((x, y), (y, x)):
            if ap in (a1, a2):
                bp[o] += 1
    for v in bp:
        assert deg[v] - bp[v] == D - bp[v]
    paths, nD, sing = convert(chosen, a1, a2, rnd, host_mode)
    # verify
    assert len(paths) == D, (len(paths), D)
    ends = {v: 0 for v in bp}
    used = set()
    for P in paths:
        assert len(P) >= 2 and len(P) == len(set(P))
        ends[P[0]] += 1
        ends[P[-1]] += 1
        for x, y in zip(P, P[1:]):
            e = (min(x, y), max(x, y))
            assert e in R and e not in used
            used.add(e)
    assert used == R
    assert all(ends[v] == bp[v] for v in bp)
    return len(sing)


if __name__ == '__main__':
    rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
    tot = 0
    hist = {}
    for N in (9, 11, 13, 21, 31, 41, 61):
        for D in range(4, N - 1, 2):
            if D // 2 > (N - 1) // 2 - 1:
                continue
            for force in (0, 1, 2, 3):
                for host in ('random', 'same'):
                    for _ in range(3):
                        ns = trial(N, D, rnd, force, host)
                        hist[ns] = hist.get(ns, 0) + 1
                        tot += 1
    print(f'{tot} conversions checked (N odd in 9..61, D even 4..N-3), all gave exactly D paths')
    print('with b\'(v) ends at every v and an exact partition of E(R).')
    print('number of singular vertices per instance -> count:', dict(sorted(hist.items())))

#!/usr/bin/env python3
"""Independent checker for witness lines "g6 p1 p2 ..." (paths "a-b-c").

Re-decodes graph6 itself (no shared code with psolve.h) and checks that the
paths are simple paths of the graph, pairwise edge-disjoint, cover every edge,
and that every vertex x is an end of exactly b(x) paths, where by default
b(x) = deg(x) mod 2 (tightness).  With --profile, each line carries the target
as a trailing field "b=1,0,2,..." and that target is used instead.
Prints the number of lines checked; exits non-zero on the first failure.
"""
import sys


def g6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits.extend((v >> k) & 1 for k in range(5, -1, -1))
    E = set()
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                E.add((i, j))
            k += 1
    return n, E


def check(line, profile=False):
    f = line.split()
    s, rest = f[0], f[1:]
    target = None
    if profile:
        assert rest[-1].startswith('b='), 'missing profile'
        target = [int(t) for t in rest[-1][2:].split(',')]
        rest = rest[:-1]
    n, E = g6(s)
    deg = [0] * n
    for i, j in E:
        deg[i] += 1
        deg[j] += 1
    if target is None:
        target = [d % 2 for d in deg]
    used = set()
    ends = [0] * n
    for p in rest:
        vs = [int(t) for t in p.split('-')]
        assert len(vs) >= 2, ('short path', p)
        assert len(set(vs)) == len(vs), ('repeated vertex', p)
        for a, b in zip(vs, vs[1:]):
            e = (min(a, b), max(a, b))
            assert e in E, ('non-edge', e, p)
            assert e not in used, ('edge twice', e)
            used.add(e)
        ends[vs[0]] += 1
        ends[vs[-1]] += 1
    assert used == E, ('uncovered edges', E - used)
    assert ends == target, ('end profile', ends, target)
    return len(rest)


def main():
    profile = '--profile' in sys.argv
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    cnt = 0
    for fn in files:
        for line in open(fn):
            if line.strip():
                check(line, profile)
                cnt += 1
    print('checked', cnt, 'witnesses: all valid')


if __name__ == '__main__':
    main()

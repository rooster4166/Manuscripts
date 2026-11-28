"""a40lib.py -- A40 audit helpers (independent of manuscripts/ln/scripts).

graph6 decoding/encoding, a decomposition checker, and a wrapper around trsolve (the audit's own
transition-system solver)."""
import subprocess, os

HERE = os.path.dirname(os.path.abspath(__file__))
TRSOLVE = os.path.join(HERE, 'trsolve')


def dec(s):
    s = s.strip()
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        x = ord(ch) - 63
        for i in range(5, -1, -1):
            bits.append((x >> i) & 1)
    A = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                A[i].add(j); A[j].add(i)
            k += 1
    return n, A


def enc(n, A):
    bits = [1 if j in A[i] else 0 for j in range(1, n) for i in range(j)]
    bits += [0] * (-len(bits) % 6)
    return chr(63 + n) + ''.join(chr(63 + int(''.join(map(str, bits[i:i + 6])), 2))
                                 for i in range(0, len(bits), 6))


def check(n, A, paths, req=None, avoid=(), sep=(), joins=()):
    """Return None if `paths` is a path decomposition of the graph with end counts `req`
    (default: degree mod 2) satisfying: for (t, a) in avoid the unique path ending at t misses a;
    for (p, q) in sep no path contains both; for (p, q) in joins some path has ends p, q."""
    if req is None:
        req = [len(A[v]) % 2 for v in range(n)]
    E = {frozenset((u, v)) for u in range(n) for v in A[u]}
    seen = set()
    ends = [0] * n
    for P in paths:
        if len(P) < 2:
            return 'short path'
        if len(set(P)) != len(P):
            return 'repeated vertex'
        for x, y in zip(P, P[1:]):
            e = frozenset((x, y))
            if e not in E:
                return 'non-edge'
            if e in seen:
                return 'edge twice'
            seen.add(e)
        ends[P[0]] += 1; ends[P[-1]] += 1
    if seen != E:
        return 'not covering'
    if ends != list(req):
        return 'end counts'
    for t, a in avoid:
        Q = [P for P in paths if t in (P[0], P[-1])]
        if len(Q) != 1:
            return 'tail end count'
        if a in Q[0]:
            return 'avoid violated'
    for p, q in sep:
        if any(p in P and q in P for P in paths):
            return 'sep violated'
    for p, q in joins:
        if not any({P[0], P[-1]} == {p, q} for P in paths):
            return 'join violated'
    return None


def parse_paths(s):
    return [list(map(int, x.split('-'))) for x in s.split(';') if x.strip()]


def solve_lines(lines, budget=None):
    args = [TRSOLVE] + (['-b', str(budget)] if budget else [])
    out = subprocess.run(args, input='\n'.join(lines) + '\n', capture_output=True, text=True).stdout
    res = []
    for o in out.splitlines():
        if o.startswith('SAT'):
            res.append(('SAT', parse_paths(o.split('::', 1)[1])))
        else:
            res.append((o.split()[0], None))
    assert len(res) == len(lines), (len(res), len(lines))
    return res

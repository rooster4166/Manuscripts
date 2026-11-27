"""Audit A22c: Python wrapper around dsolve.c plus an independent verifier.

Graphs are (n, edges) with edges a list of (u, v) pairs (parallel edges allowed).
A decomposition is a list of paths; a path is (verts, eids) with len(eids) = len(verts) - 1.
"""
import ctypes, os, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
SO = os.path.join(HERE, 'libdsolve.so')
if not os.path.exists(SO) or os.path.getmtime(SO) < os.path.getmtime(os.path.join(HERE, 'dsolve.c')):
    subprocess.check_call(['gcc', '-O2', '-shared', '-fPIC', '-o', SO, os.path.join(HERE, 'dsolve.c')])
_lib = ctypes.CDLL(SO)
_lib.dsolve.restype = ctypes.c_int
_lib.dsolve.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_int),
                        ctypes.c_uint64, ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_int),
                        ctypes.c_int, ctypes.POINTER(ctypes.c_uint64), ctypes.POINTER(ctypes.c_int),
                        ctypes.c_uint64, ctypes.c_uint64, ctypes.POINTER(ctypes.c_int), ctypes.c_int]
OUTCAP = 1 << 14
_out = (ctypes.c_int * OUTCAP)()


class Budget(Exception):
    pass


def solve(n, edges, ends, seps=(), sets=None, spec=None, seed=1, budget=0):
    """ends: set of vertices with exactly one end (all others none).  seps: pairs.  sets: list of vertex
    sets (cover constraint) or None.  spec: dict eid -> prescribed end vertex or -1 (special edge).
    Returns a decomposition, None if none exists, raises Budget if the budget ran out."""
    m = len(edges)
    eu = (ctypes.c_int * max(m, 1))(*[e[0] for e in edges])
    ev = (ctypes.c_int * max(m, 1))(*[e[1] for e in edges])
    bm = 0
    for v in ends:
        bm |= 1 << v
    seps = list(seps)
    su = (ctypes.c_int * max(len(seps), 1))(*[p[0] for p in seps])
    sv = (ctypes.c_int * max(len(seps), 1))(*[p[1] for p in seps])
    if sets is None:
        nS, S = 0, (ctypes.c_uint64 * 1)()
    else:
        masks = []
        for s in sets:
            x = 0
            for v in s:
                x |= 1 << v
            masks.append(x)
        masks = list(dict.fromkeys(masks))
        nS, S = len(masks), (ctypes.c_uint64 * max(len(masks), 1))(*masks)
    sp = [-2] * m
    if spec:
        for e, x in spec.items():
            sp[e] = x
    spa = (ctypes.c_int * max(m, 1))(*sp)
    r = _lib.dsolve(n, m, eu, ev, bm, len(seps), su, sv, nS, S, spa, seed, budget, _out, OUTCAP)
    if r == 2:
        raise Budget()
    if r < 0:
        raise RuntimeError('dsolve error %d' % r)
    if r == 0:
        return None
    D, i = [], 0
    while _out[i] != -1:
        L = _out[i]; i += 1
        vs = [_out[i]]; es = []; i += 1
        for _ in range(L):
            es.append(_out[i]); vs.append(_out[i + 1]); i += 2
        D.append((vs, es))
    return D


def endcount(D, v):
    return sum((P[0][0] == v) + (P[0][-1] == v) for P in D)


def check_decomp(n, edges, D, ends=None):
    """independent verifier: paths are simple, consecutive vertices joined by the named edge, every
    edge used exactly once; if ends given, end counts are exactly 1 on ends and 0 elsewhere."""
    used = [0] * len(edges)
    for vs, es in D:
        assert len(es) == len(vs) - 1 and len(es) >= 1, 'bad path length'
        assert len(set(vs)) == len(vs), 'path repeats a vertex'
        for i, e in enumerate(es):
            a, b = edges[e]
            assert {a, b} == {vs[i], vs[i + 1]}, 'edge does not join consecutive vertices'
            used[e] += 1
    assert all(u == 1 for u in used), 'edges not partitioned'
    if ends is not None:
        for v in range(n):
            assert endcount(D, v) == (1 if v in ends else 0), 'end count wrong at %d' % v
    return True


def degrees(n, edges):
    d = [0] * n
    for a, b in edges:
        d[a] += 1; d[b] += 1
    return d


def lovasz_ends(n, edges):
    d = degrees(n, edges)
    return {v for v in range(n) if d[v] % 2 == 1}


def path_of_end(D, v):
    """the unique path with an end at v"""
    c = [P for P in D if P[0][0] == v or P[0][-1] == v]
    assert len(c) == 1, (v, c)
    return c[0]


def terminal_at(P, e, x):
    vs, es = P
    return (vs[0] == x and es[0] == e) or (vs[-1] == x and es[-1] == e)


def check_constraints(D, seps=(), sets=None, spec=None):
    for vs, es in D:
        S = set(vs)
        for a, b in seps:
            assert not (a in S and b in S), 'separation violated'
        if sets is not None:
            assert any(S <= set(s) for s in sets), 'cover violated'
        if spec:
            sp = [e for e in es if e in spec]
            assert len(sp) <= 1, 'two special edges on a path'
            if sp:
                e = sp[0]
                atA, atC = es[0] == e, es[-1] == e
                assert atA or atC, 'special edge not terminal'
                x = spec[e]
                assert x < 0 or (atA and vs[0] == x) or (atC and vs[-1] == x), 'prescribed end violated'
    return True

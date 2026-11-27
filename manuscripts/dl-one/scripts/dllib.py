"""dllib.py: helpers for DL(1) experiments (session claude/dl-one).

Graphs are (n, edges) with edges as sorted pairs.  Decompositions are lists of vertex lists.
"""
import itertools
import os
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))


def g6_decode(s):
    s = s.strip()
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for k in range(5, -1, -1):
            bits.append((v >> k) & 1)
    edges = []
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                edges.append((i, j))
            p += 1
    return n, edges


def adjsets(n, edges):
    A = [set() for _ in range(n)]
    for u, v in edges:
        A[u].add(v)
        A[v].add(u)
    return A


def degrees(n, edges):
    d = [0] * n
    for u, v in edges:
        d[u] += 1
        d[v] += 1
    return d


def even_vertices(n, edges):
    d = degrees(n, edges)
    return [v for v in range(n) if d[v] > 0 and d[v] % 2 == 0]


def enum_decomps(n, edges, cap=200000):
    """all Lovasz decompositions (b = d mod 2), via enum.c; returns (list, complete?)"""
    inp = "%d %d %s\n" % (n, len(edges), " ".join("%d %d" % e for e in edges))
    out = subprocess.run([os.path.join(HERE, "enum"), str(cap)], input=inp, capture_output=True,
                         text=True).stdout
    res = []
    complete = True
    for line in out.splitlines():
        if line.startswith("END"):
            complete = line.split()[1] != "CAP"
            break
        res.append([list(map(int, p.split())) for p in line.split("|")] if line else [])
    return res, complete


def is_lovasz(n, edges, D):
    d = degrees(n, edges)
    es = set()
    ends = [0] * n
    for P in D:
        if len(P) < 2 or len(set(P)) != len(P):
            return False
        for x, y in zip(P, P[1:]):
            e = (min(x, y), max(x, y))
            if e in es:
                return False
            es.add(e)
        ends[P[0]] += 1
        ends[P[-1]] += 1
    if es != set(map(tuple, map(sorted, edges))):
        return False
    return all(ends[v] == d[v] % 2 for v in range(n))


def endpath(D, v):
    """index of the unique path with an end at v (None if none)"""
    r = [i for i, P in enumerate(D) if P[0] == v or P[-1] == v]
    return r[0] if len(r) == 1 else (None if not r else -1)


def Q(D, v):
    i = endpath(D, v)
    return None if i is None or i < 0 else D[i]


def dl_good(D, a, b):
    return a not in Q(D, b) or b not in Q(D, a)


def fan_transfer(D, t, w):
    """Fan transfer t -> w with the forced chain, on a decomposition D of K (b <= 1, tw not an
    edge of K, b(t) = 1); returns (new decomposition of K + tw, chain list)."""
    cur = [list(P) for P in D]
    orig_end = {}
    for i, P in enumerate(D):
        orig_end.setdefault(P[0], []).append(i)
        orig_end.setdefault(P[-1], []).append(i)
    x = t
    chain = [t]
    while True:
        ids = orig_end.get(x, [])
        assert len(ids) == 1, "vertex %d has %d ends" % (x, len(ids))
        pid = ids[0]
        P = cur[pid]
        if P[-1] == x:
            P = P[::-1]
        assert P[0] == x
        if w not in P:
            cur[pid] = [w] + P
            return cur, chain
        k = P.index(w)
        y = P[k - 1]
        assert y != x
        cur[pid] = P[:k][::-1] + P[k:]
        x = y
        assert x not in chain, "chain repeats"
        chain.append(x)


def univ_twins(n, edges, a, b):
    A = adjsets(n, edges)
    # component of a
    seen = {a}
    st = [a]
    while st:
        x = st.pop()
        for y in A[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    if b not in seen:
        return False
    rest = seen - {a, b}
    return A[a] == rest and A[b] == rest


def remove_edge(edges, u, v):
    e = (min(u, v), max(u, v))
    return [x for x in edges if x != e]

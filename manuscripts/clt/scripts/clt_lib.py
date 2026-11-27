"""clt_lib.py: helpers for constrained Lovász tests (session claude/clt).

Graphs are (n, adj) with adj a list of sets.  A *system* is a dict with keys
  'ef' : {v: set S}      the path ending at v avoids S
  'ep' : [(u, v)]        no path has ends exactly u, v
  'es' : [(p, q, S)]     the path through the edge pq has its end on p's side outside S
                         (terminal edge pq at p:  es (p, q, V - {p}))
  'sep': [(a, b)]        no path contains both a and b
Instances are decided by manuscripts/t6-dense/scripts/lsearch.c (exact DFS with memo; compiled to
LSEARCH).  `solve_many` streams a list of (graph, system) and returns 'OK'/'NONE'/'UND' with the
witness paths for 'OK'.
"""
import os
import subprocess

LSEARCH = os.environ.get('LSEARCH', '/tmp/claude-0/lsearch')


def parse_g6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for k in range(5, -1, -1):
            bits.append((v >> k) & 1)
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return n, adj


def to_g6(n, adj):
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if j in adj[i] else 0)
    while len(bits) % 6:
        bits.append(0)
    s = chr(n + 63)
    for i in range(0, len(bits), 6):
        v = 0
        for b in bits[i:i + 6]:
            v = 2 * v + b
        s += chr(v + 63)
    return s


def even_vertices(n, adj):
    return [v for v in range(n) if adj[v] and len(adj[v]) % 2 == 0]


def block(n, adj, sysd, seed=0, budget=0, b=None):
    edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
    if b is None:
        b = [len(adj[v]) % 2 for v in range(n)]
    L = [f"{n} {len(edges)} {seed} {budget}", ' '.join(f"{u} {v}" for u, v in edges), ' '.join(map(str, b))]
    sep = sysd.get('sep', [])
    L.append(' '.join([str(len(sep))] + [f"{a} {c}" for a, c in sep]))
    ef = sysd.get('ef', {})
    efl = [(v, S) for v, S in ef.items() if S]
    L.append(' '.join([str(len(efl))] + [f"{v} {len(S)} " + ' '.join(map(str, sorted(S))) for v, S in efl]))
    ep = sysd.get('ep', [])
    L.append(' '.join([str(len(ep))] + [f"{a} {c}" for a, c in ep]))
    es = sysd.get('es', [])
    L.append(' '.join([str(len(es))] + [f"{p} {q} {len(S)} " + ' '.join(map(str, sorted(S))) for p, q, S in es]))
    return '\n'.join(L) + '\n'


def solve_many(items, budget=0, seed=0):
    """items: list of (n, adj, sysd).  Returns list of (status, paths)."""
    inp = ''.join(block(n, adj, s, seed, budget) for n, adj, s in items)
    out = subprocess.run([LSEARCH], input=inp, capture_output=True, text=True).stdout.split('\n')
    res = []
    i = 0
    for _ in items:
        line = out[i]
        i += 1
        if line.startswith('OK'):
            k = int(line.split()[1])
            paths = [list(map(int, out[i + j].split())) for j in range(k)]
            i += k
            res.append(('OK', paths))
        else:
            res.append((line.strip(), None))
    return res


def check(n, adj, paths, sysd):
    """Independent check of a witness: decomposition, Lovász ends, and every constraint."""
    E = set()
    for P in paths:
        if len(set(P)) != len(P):
            return False
        for a, c in zip(P, P[1:]):
            if c not in adj[a]:
                return False
            e = frozenset((a, c))
            if e in E:
                return False
            E.add(e)
    if len(E) != sum(len(a) for a in adj) // 2:
        return False
    ends = [0] * n
    for P in paths:
        ends[P[0]] += 1
        ends[P[-1]] += 1
    if any(ends[v] != len(adj[v]) % 2 for v in range(n)):
        return False
    endpath = {}
    for P in paths:
        endpath[P[0]] = P
        endpath[P[-1]] = P
    for v, S in sysd.get('ef', {}).items():
        if set(endpath[v]) & set(S):
            return False
    for u, v in sysd.get('ep', []):
        if endpath[u] is endpath[v]:
            return False
    for p, q, S in sysd.get('es', []):
        for P in paths:
            for i in range(len(P) - 1):
                if (P[i], P[i + 1]) == (p, q) and P[0] in S:
                    return False
                if (P[i], P[i + 1]) == (q, p) and P[-1] in S:
                    return False
    for a, c in sysd.get('sep', []):
        if any(a in P and c in P for P in paths):
            return False
    return True

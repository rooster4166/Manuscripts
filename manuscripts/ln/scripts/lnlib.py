"""lnlib.py -- graph6, witness checking and an independent brute-force solver (ln session).

The brute force enumerates all simple paths of a graph and solves the exact cover of the edge set
by paths with prescribed end counts and constraints, by plain recursion on the lowest uncovered
edge.  It shares no code with lnsolve.c and is used to validate it on small graphs."""
import itertools, sys

def g6_decode(s):
    s = s.strip()
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits.extend((v >> (5 - i)) & 1 for i in range(6))
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j); adj[j].add(i)
            k += 1
    return n, adj

def g6_encode(n, adj):
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if j in adj[i] else 0)
    while len(bits) % 6:
        bits.append(0)
    out = chr(n + 63)
    for i in range(0, len(bits), 6):
        v = 0
        for b in bits[i:i + 6]:
            v = 2 * v + b
        out += chr(v + 63)
    return out

def edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]

def parse_instance(line):
    t = line.split()
    n, adj = g6_decode(t[0])
    req = [len(adj[v]) % 2 for v in range(n)]
    av, sep = [], []
    i = 1
    while i < len(t):
        if t[i] == 'A':
            av.append((int(t[i + 1]), int(t[i + 2]))); i += 3
        elif t[i] == 'S':
            sep.append((int(t[i + 1]), int(t[i + 2]))); i += 3
        elif t[i] == 'J':
            sep.append(('J', int(t[i + 1]), int(t[i + 2]))); i += 3
        elif t[i] == 'R':
            req[int(t[i + 1])] = int(t[i + 2]); i += 3
        else:
            raise ValueError(t[i])
    return n, adj, req, av, sep

def check_witness(n, adj, req, av, sep, paths):
    """paths: list of vertex lists. Returns None if valid, else an error string."""
    used = set()
    ends = [0] * n
    for P in paths:
        if len(P) < 2 or len(set(P)) != len(P):
            return 'not a simple path %s' % P
        for a, b in zip(P, P[1:]):
            if b not in adj[a]:
                return 'non-edge %d-%d' % (a, b)
            e = (min(a, b), max(a, b))
            if e in used:
                return 'edge used twice %s' % (e,)
            used.add(e)
        ends[P[0]] += 1; ends[P[-1]] += 1
    if used != set(edges(n, adj)):
        return 'edges not covered'
    if ends != list(req):
        return 'end counts %s != %s' % (ends, req)
    for (t, a) in av:
        Ps = [P for P in paths if P[0] == t or P[-1] == t]
        if len(Ps) != 1:
            return 'tail %d has %d end paths' % (t, len(Ps))
        if a in Ps[0]:
            return 'avoid %d %d violated' % (t, a)
    for s in sep:
        if s[0] == 'J':
            if not any({P[0], P[-1]} == {s[1], s[2]} for P in paths):
                return 'join %d %d violated' % (s[1], s[2])
            continue
        p, q = s
        for P in paths:
            if p in P and q in P:
                return 'separation %d %d violated' % (p, q)
    return None

def parse_witness(s):
    paths = []
    for part in s.split(';'):
        part = part.strip()
        if part:
            paths.append([int(x) for x in part.split('-')])
    return paths

def all_paths(n, adj):
    res = []
    def ext(P, S):
        if len(P) >= 2 and P[0] < P[-1]:
            res.append(tuple(P))
        for y in adj[P[-1]]:
            if y not in S:
                P.append(y); S.add(y)
                ext(P, S)
                P.pop(); S.discard(y)
    for v in range(n):
        ext([v], {v})
    return res

def brute(n, adj, req, av, sep):
    """exact cover; returns a list of paths or None."""
    E = edges(n, adj)
    eidx = {e: i for i, e in enumerate(E)}
    paths = all_paths(n, adj)
    byedge = [[] for _ in E]
    pinfo = []
    for P in paths:
        es = [eidx[(min(a, b), max(a, b))] for a, b in zip(P, P[1:])]
        ok = True
        for (t, a) in av:
            if (P[0] == t or P[-1] == t) and a in P:
                ok = False
        for s in sep:
            if s[0] == 'J':
                if (P[0] in s[1:] or P[-1] in s[1:]) and {P[0], P[-1]} != set(s[1:]):
                    ok = False
                continue
            p, q = s
            if p in P and q in P:
                ok = False
        if not ok:
            continue
        k = len(pinfo)
        pinfo.append((P, es))
        for e in es:
            byedge[e].append(k)
    covered = [False] * len(E)
    ends = [0] * n
    chosen = []
    def rec():
        try:
            e = covered.index(False)
        except ValueError:
            return ends == list(req)
        for k in byedge[e]:
            P, es = pinfo[k]
            if any(covered[f] for f in es):
                continue
            a, b = P[0], P[-1]
            if ends[a] + 1 > req[a] or ends[b] + 1 > req[b]:
                continue
            for f in es: covered[f] = True
            ends[a] += 1; ends[b] += 1; chosen.append(list(P))
            if rec():
                return True
            for f in es: covered[f] = False
            ends[a] -= 1; ends[b] -= 1; chosen.pop()
        return False
    # avoid constraints with tails: tail must have exactly one end path (req = 1), enforced by req
    if rec():
        return chosen
    return None

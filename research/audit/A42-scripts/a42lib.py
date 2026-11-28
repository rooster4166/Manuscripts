"""A42 audit library (own code; shares nothing with lnlib.py / routeR.py)."""
def g6dec(s):
    s = s.strip(); n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        x = ord(ch) - 63
        for k in range(5, -1, -1): bits.append((x >> k) & 1)
    adj = [set() for _ in range(n)]; k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]: adj[i].add(j); adj[j].add(i)
            k += 1
    return n, adj

def g6enc(n, adj):
    bits = []
    for j in range(1, n):
        for i in range(j): bits.append(1 if j in adj[i] else 0)
    while len(bits) % 6: bits.append(0)
    s = chr(63 + n)
    for k in range(0, len(bits), 6):
        x = 0
        for b in bits[k:k + 6]: x = 2 * x + b
        s += chr(63 + x)
    return s

def comp_of(adj, s, banned=()):
    banned = set(banned)
    seen = {s}; st = [s]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen and v not in banned: seen.add(v); st.append(v)
    return seen

def edges(adj):
    return sorted((u, v) for u in range(len(adj)) for v in adj[u] if u < v)

def check(n, adj, paths, req=None, avoid=(), sep=(), join=()):
    """Own witness checker. paths: list of vertex lists. req[v] = required ends (default d mod 2).
    avoid: (t, a): every path with an end at t misses a. sep: (p, q): no path contains both.
    join: (p, q): some path has ends exactly {p, q}. Returns None or an error string."""
    if req is None: req = [len(adj[v]) % 2 for v in range(n)]
    used = set(); ends = [0] * n
    for P in paths:
        if len(P) < 2: return 'short path'
        if len(set(P)) != len(P): return 'repeated vertex'
        for v in P:
            if not (0 <= v < n): return 'bad vertex'
        for a, b in zip(P, P[1:]):
            if b not in adj[a]: return 'non-edge'
            e = (min(a, b), max(a, b))
            if e in used: return 'edge twice'
            used.add(e)
        ends[P[0]] += 1; ends[P[-1]] += 1
    if used != set(edges(adj)): return 'edges not covered'
    if ends != list(req): return 'end counts'
    for t, a in avoid:
        for P in paths:
            if (P[0] == t or P[-1] == t) and a in P: return 'avoid violated'
    for p, q in sep:
        for P in paths:
            if p in P and q in P: return 'sep violated'
    for p, q in join:
        if not any({P[0], P[-1]} == {p, q} for P in paths): return 'join violated'
    return None

def parse_query(q):
    t = q.split(); n, adj = g6dec(t[0])
    req = [len(adj[v]) % 2 for v in range(n)]; avoid = []; sep = []; join = []
    i = 1
    while i < len(t):
        k, x, y = t[i], int(t[i + 1]), int(t[i + 2]); i += 3
        if k == 'A': avoid.append((x, y))
        elif k == 'S': sep.append((x, y))
        elif k == 'J': join.append((x, y))
        elif k == 'R': req[x] = y
        else: raise ValueError(k)
    return n, adj, req, avoid, sep, join

def parse_answer(a):
    a = a.strip()
    if not a.startswith('SAT'): return a.split()[0] if a else '', None
    w = a.split('::', 1)[1]
    paths = [[int(x) for x in p.strip().split('-')] for p in w.split(';') if p.strip()]
    return 'SAT', paths

def check_qa(q, a):
    st, paths = parse_answer(a)
    if st != 'SAT': return st
    n, adj, req, avoid, sep, join = parse_query(q)
    if a.split()[1] != q.split()[0]: return 'graph mismatch'
    err = check(n, adj, paths, req, avoid, sep, join)
    return 'OK' if err is None else 'FAIL ' + err

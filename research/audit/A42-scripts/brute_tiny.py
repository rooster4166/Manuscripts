"""A42: label brute force for tiny graphs (independent of every solver): with k = (sum r)/2
paths, try every map edges -> {0..k-1} (canonical: labels appear in first-use order), and accept
if every class is a simple path whose ends are distributed as r, and the constraints hold.
Compares with a42solve, lnsolve3 and lnsolve on random queries (graphs with even vertices,
R, J, A, S constraints)."""
import sys, random, subprocess, itertools
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import g6enc, parse_query, check

def as_path(es):
    # es: list of edges; return vertex list if they form a simple path, else None
    deg = {}
    for u, v in es: deg[u] = deg.get(u, 0) + 1; deg[v] = deg.get(v, 0) + 1
    if any(d > 2 for d in deg.values()): return None
    ends = [v for v, d in deg.items() if d == 1]
    if len(ends) != 2: return None
    adj = {}
    for u, v in es: adj.setdefault(u, []).append(v); adj.setdefault(v, []).append(u)
    P = [ends[0]]; prev = None
    while True:
        nx = [w for w in adj[P[-1]] if w != prev]
        if not nx: break
        prev = P[-1]; P.append(nx[0])
        if len(P) > len(es) + 1: return None
    if len(P) != len(es) + 1: return None
    return P

def brute(q):
    n, adj, req, avoid, sep, join = parse_query(q)
    E = sorted((u, v) for u in range(n) for v in adj[u] if u < v)
    tot = sum(req)
    if tot % 2 or any((len(adj[v]) - req[v]) % 2 for v in range(n)): return 'UNSAT'
    k = tot // 2
    if k == 0: return 'SAT' if not E else 'UNSAT'
    m = len(E)
    lab = [0] * m
    def rec(i, used):
        if i == m:
            if used != k: return False
            cls = [[] for _ in range(k)]
            for e, l in zip(E, lab): cls[l].append(e)
            paths = []
            for c in cls:
                P = as_path(c)
                if P is None: return False
                paths.append(P)
            return check(n, adj, paths, req, avoid, sep, join) is None
        for l in range(min(used + 1, k)):
            lab[i] = l
            if rec(i + 1, max(used, l + 1)): return True
        return False
    return 'SAT' if rec(0, 0) else 'UNSAT'

random.seed(int(sys.argv[1])); N = int(sys.argv[2])
Q = []
while len(Q) < N:
    n = random.randint(4, 7)
    adj = [set() for _ in range(n)]
    m = 0
    for u in range(n):
        for v in range(u + 1, n):
            if random.random() < 0.45: adj[u].add(v); adj[v].add(u); m += 1
    if m == 0 or m > 9: continue
    q = g6enc(n, adj)
    req = [len(adj[v]) % 2 for v in range(n)]
    for _ in range(random.randint(0, 3)):
        typ = random.choice('AASJR'); x, y = random.sample(range(n), 2)
        if typ == 'R':
            if len(adj[x]) >= 2 and random.random() < 0.5:
                k = len(adj[x]) % 2 + 2 * random.randint(0, 1)
                if k <= 2: req[x] = k; q += ' R %d %d' % (x, k)
            continue
        if typ == 'A':
            if req[x] != 1: continue
        if typ == 'J':
            if req[x] != 1 or req[y] != 1: continue
        q += ' %s %d %d' % (typ, x, y)
    Q.append(q)
inp = '\n'.join(Q) + '\n'
res = {}
for name, cmd in (('a42solve', ['./a42solve']), ('lnsolve3', ['./lnsolve3']), ('lnsolve', ['./lnsolve'])):
    res[name] = [l.split()[0] for l in subprocess.run(cmd, input=inp, capture_output=True, text=True).stdout.split('\n')[:len(Q)]]
dis = 0; sat = 0
for i, q in enumerate(Q):
    b = brute(q); sat += b == 'SAT'
    for name in res:
        if res[name][i] != b and not (name != 'a42solve' and res[name][i] == 'BADTAIL'):
            dis += 1; print('DISAGREE', name, q, res[name][i], 'brute', b)
print('tiny queries', len(Q), 'brute SAT', sat, 'disagreements', dis)

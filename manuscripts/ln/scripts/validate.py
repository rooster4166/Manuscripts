"""validate.py -- cross-check lnsolve against the brute force of lnlib on random instances.
usage: python3 validate.py LNSOLVE maxn count seed"""
import sys, random, subprocess
from lnlib import *
solver, maxn, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rng = random.Random(seed)
lines = []
for _ in range(count):
    n = rng.randint(3, maxn)
    p = rng.uniform(0.25, 0.8)
    adj = [set() for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                adj[i].add(j); adj[j].add(i)
    if rng.random() < 0.8:
        ev = [v for v in range(n) if len(adj[v]) % 2 == 0 and adj[v]]
        keep = 1 if rng.random() < 0.5 else 0
        for v in ev[keep:]:
            if n >= 9: break
            adj.append({v}); adj[v].add(n); n += 1
    req = [len(adj[v]) % 2 for v in range(n)]
    toks = [g6_encode(n, adj)]
    odd = [v for v in range(n) if req[v] == 1]
    for _ in range(rng.randint(0, 3)):
        if odd and rng.random() < 0.7:
            t = rng.choice(odd); a = rng.randrange(n)
            if a != t: toks += ['A', str(t), str(a)]
        else:
            p_, q_ = rng.randrange(n), rng.randrange(n)
            if p_ != q_: toks += ['S', str(p_), str(q_)]
    lines.append(' '.join(toks))
out = subprocess.run([solver], input='\n'.join(lines) + '\n', capture_output=True, text=True).stdout.splitlines()
assert len(out) == len(lines)
stats = {'SAT': 0, 'UNSAT': 0, 'mismatch': 0, 'badwit': 0}
for L, O in zip(lines, out):
    n, adj, req, av, sep = parse_instance(L)
    b = brute(n, adj, req, av, sep)
    if O.startswith('SAT'):
        stats['SAT'] += 1
        err = check_witness(n, adj, req, av, sep, parse_witness(O.split('::', 1)[1]))
        if err: stats['badwit'] += 1; print('BADWIT', L, err)
        if b is None: stats['mismatch'] += 1; print('MISMATCH (solver SAT, brute UNSAT)', L)
    elif O.startswith('UNSAT'):
        stats['UNSAT'] += 1
        if b is not None: stats['mismatch'] += 1; print('MISMATCH (solver UNSAT, brute SAT)', L, b)
    else:
        print('OTHER', O)
print(stats)

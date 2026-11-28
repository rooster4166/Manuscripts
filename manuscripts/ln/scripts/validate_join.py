"""validate_join.py LNSOLVE count seed -- cross-check of the joined-ends constraint J p q.

Random all-odd graphs of order 6 or 8 (edge probability 1/2, resampled until every degree is odd),
a constraint J c1 c2 and 0-2 constraints A c1 a; lnsolve is compared with lnlib.brute and every SAT
witness is re-checked by lnlib.check_witness.  Run in the session with count 600, seed 3."""
import random, subprocess, sys
from lnlib import g6_encode, parse_instance, brute, check_witness, parse_witness
solver, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed); L = []
for _ in range(count):
    n = rng.choice([6, 8])
    while True:
        adj = [set() for _ in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < 0.5: adj[i].add(j); adj[j].add(i)
        if all(len(a) % 2 == 1 for a in adj): break
    c1, c2 = rng.sample(range(n), 2)
    toks = [g6_encode(n, adj), 'J', str(c1), str(c2)]
    for _ in range(rng.randint(0, 2)):
        a = rng.randrange(n)
        if a not in (c1, c2): toks += ['A', str(c1), str(a)]
    L.append(' '.join(toks))
out = subprocess.run([solver], input='\n'.join(L) + '\n', capture_output=True, text=True).stdout.split('\n')
stats = {'SAT': 0, 'UNSAT': 0, 'mismatch': 0, 'badwit': 0}
for l, o in zip(L, out):
    n, adj, req, av, sep = parse_instance(l); b = brute(n, adj, req, av, sep)
    if o.startswith('SAT'):
        stats['SAT'] += 1
        e = check_witness(n, adj, req, av, sep, parse_witness(o.split('::', 1)[1]))
        if e: stats['badwit'] += 1; print('BADWIT', l, e)
        if b is None: stats['mismatch'] += 1; print('MISMATCH (solver SAT, brute UNSAT)', l)
    else:
        stats['UNSAT'] += 1
        if b is not None: stats['mismatch'] += 1; print('MISMATCH (solver UNSAT, brute SAT)', l)
print(stats, flush=True)

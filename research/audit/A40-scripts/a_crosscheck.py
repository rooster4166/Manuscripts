"""a_crosscheck.py -- (a) cross-check lnsolve (session) against trsolve (audit) on random instances.
usage: python3 a_crosscheck.py LNSOLVE count seed maxn [cap]  (cap: max order after hanging leaves)
Every SAT witness of either solver is checked with a40lib.check; answers must agree."""
import sys, random, subprocess
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a40lib import dec, enc, check, parse_paths, solve_lines

lnsolve, count, seed, maxn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
cap = int(sys.argv[5]) if len(sys.argv) > 5 else maxn
rng = random.Random(seed)
inst = []
while len(inst) < count:
    n = rng.randint(3, maxn)
    p = rng.uniform(0.2, 0.85)
    A = [set() for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                A[i].add(j); A[j].add(i)
    mode = rng.random()
    if mode < 0.6:  # make at most one even vertex by hanging leaves (keeps n <= maxn + 2)
        ev = [v for v in range(n) if A[v] and len(A[v]) % 2 == 0]
        rng.shuffle(ev)
        for v in ev[1:]:
            if n >= cap:
                break
            A.append({v}); A[v].add(n); n += 1
    req = [len(A[v]) % 2 for v in range(n)]
    cons = []
    for _ in range(rng.randint(0, 4)):
        k = rng.random()
        if k < 0.1:
            v = rng.randrange(n); r = rng.choice([0, 1, 2])
            if all(c[1] != v for c in cons):
                cons.append(('R', v, r)); req[v] = r
    for _ in range(rng.randint(0, 4)):
        k = rng.random()
        ones = [v for v in range(n) if req[v] == 1]
        if k < 0.5 and ones:
            t = rng.choice(ones); a = rng.randrange(n)
            if a != t:
                cons.append(('A', t, a))
        elif k < 0.8:
            x, y = rng.randrange(n), rng.randrange(n)
            if x != y:
                cons.append(('S', x, y))
        elif len(ones) >= 2:
            x, y = rng.sample(ones, 2)
            if all(c[0] != 'J' or not ({c[1], c[2]} & {x, y}) for c in cons):
                cons.append(('J', x, y))
    # A/J need r = 1 at the constrained vertex
    if any(c[0] in 'AJ' and req[c[1]] != 1 for c in cons) or any(c[0] == 'J' and req[c[2]] != 1 for c in cons):
        continue
    line = enc(n, A) + ''.join(' %s %d %d' % c for c in cons)
    inst.append((line, n, A, req, cons))

lines = [x[0] for x in inst]
tr = solve_lines(lines, budget=50000000)
lo = subprocess.run([lnsolve], input='\n'.join(lines) + '\n', capture_output=True, text=True).stdout.splitlines()
stats = {'SAT': 0, 'UNSAT': 0, 'mismatch': 0, 'badwit_ln': 0, 'badwit_tr': 0, 'undec': 0}
for (line, n, A, req, cons), (ta, tw), lout in zip(inst, tr, lo):
    av = [(c[1], c[2]) for c in cons if c[0] == 'A']
    sp = [(c[1], c[2]) for c in cons if c[0] == 'S']
    jn = [(c[1], c[2]) for c in cons if c[0] == 'J']
    la = lout.split()[0]
    if 'UNDEC' in (ta, la):
        stats['undec'] += 1; print('UNDEC', line, ta, la); continue
    if ta == 'SAT':
        err = check(n, A, tw, req, av, sp, jn)
        if err: stats['badwit_tr'] += 1; print('BADWIT-tr', line, err)
    if la == 'SAT':
        err = check(n, A, parse_paths(lout.split('::', 1)[1]), req, av, sp, jn)
        if err: stats['badwit_ln'] += 1; print('BADWIT-ln', line, err)
    if ta != la:
        stats['mismatch'] += 1; print('MISMATCH', line, ta, la)
    else:
        stats[ta] += 1
ctype = {}
for (line, n, A, req, cons) in inst:
    for c in set(c[0] for c in cons):
        ctype[c] = ctype.get(c, 0) + 1
    ctype['n=%d' % n] = ctype.get('n=%d' % n, 0) + 1
print(stats)
print('instances with each constraint type / by order:', dict(sorted(ctype.items())))

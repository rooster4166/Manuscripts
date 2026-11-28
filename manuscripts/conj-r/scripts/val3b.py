"""val3.py -- compare lnsolve3 (lnsolve + joint-pair branching + degree bound) with the validated
lnsolve on random constrained queries (orders 6 and 8), and re-check every lnsolve3 witness."""
import sys, random, subprocess
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode, parse_instance, check_witness
random.seed(int(sys.argv[1]))
G8 = [l.strip() for l in open('g8.txt')]
G10 = [l.strip() for l in open('odd6c.g6')]
Q = []
for k in range(int(sys.argv[2])):
    g = random.choice(G8 if k % 2 else G10)
    n, adj = g6_decode(g)
    vs = random.sample(range(n), 4)
    c1, a1, c2, a2 = vs
    typ = random.randrange(4)
    if typ == 0: q = '%s J %d %d A %d %d A %d %d' % (g, c1, c2, c1, a1, c2, a2)
    elif typ == 1: q = '%s J %d %d' % (g, c1, c2)
    elif typ == 2: q = '%s A %d %d A %d %d' % (g, c1, a1, c2, a2)
    else:
        # remove a random path's edges: parity decomposition of F - E(P), via R constraints
        q = '%s A %d %d S %d %d' % (g, c1, a1, c2, a2)
    Q.append(q)
inp = '\n'.join(Q) + '\n'
o1 = subprocess.run(['./lnsolve', '-b', '20000000'], input=inp, capture_output=True, text=True).stdout.split('\n')
o3 = subprocess.run(['./lnsolve3', '-b', '20000000'], input=inp, capture_output=True, text=True).stdout.split('\n')
agree = dis = und = wit = 0
for q, r1, r3 in zip(Q, o1, o3):
    s1, s3 = r1.split()[0], r3.split()[0]
    if 'UNDEC' in (s1, s3): und += 1; continue
    if s1 != s3: dis += 1; print('DISAGREE', q, s1, s3); continue
    agree += 1
    if s3 == 'SAT':
        n, adj, req, av, sep = parse_instance(q)
        paths = [list(map(int, p.split('-'))) for p in r3.split('::')[1].split(';')]
        err = check_witness(n, adj, req, av, sep, paths)
        assert err is None, (q, err)
        wit += 1
print('queries', len(Q), 'agree', agree, 'disagree', dis, 'undecided', und, 'witnesses checked', wit)

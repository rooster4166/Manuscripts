"""cmp_f.py INFILE OUTFILE SAMPLE SEED: ptm 'f'-mode instances ("g6(G-F) a1 b1 a2 b2 ...", simple case);
recompute PTM and PTM(e@x) for a random sample with bf.py and compare with the failure lines of the
corresponding ptm output (lazy: stop as soon as every (e, x) has a feasible assignment)."""
import sys, itertools, random
from bf import parse_g6, ptm_assign
inf, outf, K, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
lines = open(inf).read().split('\n')
lines = [l for l in lines if l.strip()]
fails = set()
for l in open(outf):
    t = l.split()
    if t[0] in ('PTMFAIL', 'RFAIL', 'UND', 'RUND'):
        fails.add(t[1] + ' ' + ' '.join(x.rstrip('*').replace('-', ' ') for x in t[2:] if '-' in x and not x.startswith(('end', 'GF'))))
rnd = random.Random(seed)
S = rnd.sample(lines, min(K, len(lines)))
c = dict(checked=0, ptm_fail=0, r_fail=0, disagree=0)
for l in S:
    t = l.split(); n, A = parse_g6(t[0]); v = list(map(int, t[1:]))
    F = [(v[2 * i], v[2 * i + 1]) for i in range(len(v) // 2)]
    for a, b in F:
        assert not A[a][b]
        A[a][b] = A[b][a] = 1
    assert all(sum(A[u]) % 2 == 1 for u in range(n))
    c['checked'] += 1
    need = {(i, x) for i, e in enumerate(F) for x in e}
    got, anyok = set(), False
    for sh in itertools.product(*F):
        if not ({(i, s) for i, s in enumerate(sh)} - got):
            continue
        if ptm_assign(n, A, F, list(sh)):
            anyok = True
            got |= {(i, s) for i, s in enumerate(sh)}
        if got == need:
            break
    bad = (not anyok) or got != need
    c['ptm_fail'] += not anyok
    c['r_fail'] += len(need - got) if anyok else 0
    key = t[0] + ' ' + ' '.join(t[1:])
    if bad != (key in fails):
        c['disagree'] += 1
        print('DISAGREE', l)
print(inf, c)

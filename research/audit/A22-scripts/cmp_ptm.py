"""cmp_ptm.py N M OUTFILE [SAMPLE SEED]: recompute PTM / PTM(e@x) / PEE for all M-matchings of all connected
all-odd graphs of order N (nauty-geng -c N; flags from $GENG, e.g. GENG=-ctfq for girth >= 5) with bf.py, and compare with ptm's output file
(scripts/out/s_N_M.txt): failure lines and SUMMARY counts.  With SAMPLE > 0 only a random sample of
instances is checked (failure lines of the file are always included)."""
import sys, itertools, subprocess, random, time, os
from bf import parse_g6, ptm_assign

N, M, OUT = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
SAMPLE = int(sys.argv[4]) if len(sys.argv) > 4 else 0
SEED = int(sys.argv[5]) if len(sys.argv) > 5 else 1

# ptm's reported failures
fails_ptm, fails_r, summ = set(), set(), {}
for line in open(OUT):
    t = line.split()
    if t[0] == 'SUMMARY':
        summ = dict(kv.split('=') for kv in t[1:])
        continue
    pairs = frozenset(frozenset(map(int, x.rstrip('*').split('-'))) for x in t[2:] if '-' in x and not x.startswith(('end', 'GF')))
    if t[0] == 'PTMFAIL':
        fails_ptm.add((t[1], pairs))
    elif t[0] == 'RFAIL':
        end = int([x for x in t if x.startswith('end=')][0][4:])
        fails_r.add((t[1], pairs, end))

g6s = subprocess.run(['nauty-geng', os.environ.get('GENG', '-cq'), str(N)], capture_output=True, text=True).stdout.split()
inst = []
for s in g6s:
    n, A = parse_g6(s)
    if any(sum(A[v]) % 2 == 0 for v in range(n)):
        continue
    E = [(u, v) for u in range(n) for v in range(u + 1, n) if A[u][v]]
    for F in itertools.combinations(E, M):
        if len({x for e in F for x in e}) < 2 * M:
            continue
        inst.append((s, n, A, F))
total = len(inst)
if SAMPLE:
    rnd = random.Random(SEED)
    keep = set(rnd.sample(range(total), min(SAMPLE, total)))
    flagged = {(f[0], f[1]) for f in fails_ptm} | {(f[0], f[1]) for f in fails_r}
    inst = [I for k, I in enumerate(inst) if k in keep or (I[0], frozenset(frozenset(e) for e in I[3])) in flagged]

t0 = time.time()
c = dict(inst=0, ptm_fail=0, r_tests=0, r_fail=0, pee_tests=0, pee_fail=0)
my_ptm, my_r = set(), set()
for (s, n, A, F) in inst:
    c['inst'] += 1
    feas = {}
    for shorts in itertools.product(*F):
        feas[shorts] = ptm_assign(n, A, list(F), list(shorts))
    key = frozenset(frozenset(e) for e in F)
    if not any(feas.values()):
        c['ptm_fail'] += 1
        my_ptm.add((s, key))
        continue
    for i, e in enumerate(F):
        for x in e:
            c['r_tests'] += 1
            if not any(ok for sh, ok in feas.items() if sh[i] == x):
                c['r_fail'] += 1
                my_r.add((s, key, x))
    c['pee_tests'] += len(feas)
    c['pee_fail'] += sum(1 for ok in feas.values() if not ok)

print('N=%d M=%d instances in class=%d checked=%d time=%.1fs' % (N, M, total, c['inst'], time.time() - t0))
print('bf   :', c)
print('ptm  :', {k: summ.get(k) for k in c})
print('PTMFAIL agree:', my_ptm == fails_ptm, len(my_ptm), len(fails_ptm))
print('RFAIL   agree:', my_r == fails_r, len(my_r), len(fails_r))
if my_ptm != fails_ptm:
    print('  only bf:', my_ptm - fails_ptm, ' only ptm:', fails_ptm - my_ptm)
if my_r != fails_r:
    print('  only bf:', my_r - fails_r, ' only ptm:', fails_r - my_r)

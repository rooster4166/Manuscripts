"""A42: Section 4 'joint paths' and 'obstruction to tightness', recomputed: every joint path P of every
joined order-8 instance (from jcov's K0 file: 'K0g6 c1 c2 act/iso 2c/n2c O1/- | P'), tightness of
K0 = F - E(P) by a42solve; per-instance canonical rules."""
import sys, subprocess, collections
from multiprocessing import Pool
def solve(Q):
    r = subprocess.run(['./a42solve', '-b', '50000000'], input='\n'.join(Q) + '\n', capture_output=True, text=True).stdout.split('\n')
    return [x.split()[0] for x in r[:len(Q)]]
if __name__ == '__main__':
    K = [l.rstrip('\n') for l in open(sys.argv[1]) if l.strip()]
    inst = [l.strip() for l in open(sys.argv[2]) if l.strip()]   # jcov stdout, to recover instance boundaries
    Q = [l.split()[0] for l in K]
    chunks = [Q[i:i + 5000] for i in range(0, len(Q), 5000)]
    import os
    if os.path.exists(sys.argv[1] + '.ans'): res = open(sys.argv[1] + '.ans').read().split()
    else:
        with Pool(int(sys.argv[3])) as p: res = [a for r in p.map(solve, chunks) for a in r]
        open(sys.argv[1] + '.ans', 'w').write('\n'.join(res) + '\n')
    C = collections.Counter()
    for l, a in zip(K, res):
        f = l.split(' | ')[0].split()
        C[('tight' if a == 'SAT' else ('NOT' if a == 'UNSAT' else a)), f[3], f[4], f[5]] += 1
    for k in sorted(C): print(k, C[k])
    print('joint paths', len(K), 'tight', sum(a == 'SAT' for a in res), 'UNDEC', sum(a == 'UNDEC' for a in res))
    # per-instance rules: jcov prints instances in input order and paths in DFS order; the K0 file
    # lists paths in the same order; npaths per instance is field 2 after '|'
    k = 0; R = collections.Counter()
    for l in inst:
        a, b = l.split(' | '); f = b.split()
        if f[0] != 'J': continue
        npth = int(f[1]); rec = []
        for _ in range(npth):
            P = K[k].split(' | ')[1].split()[0].split('-'); rec.append((len(P) - 1, res[k] == 'SAT')); k += 1
        mn = min(L for L, _ in rec); mx = max(L for L, _ in rec)
        R['joined'] += 1; R['some joint exact'] += any(s for _, s in rec)
        R['some longest exact'] += any(s for L, s in rec if L == mx); R['every longest exact'] += all(s for L, s in rec if L == mx)
        R['some shortest exact'] += any(s for L, s in rec if L == mn); R['every shortest exact'] += all(s for L, s in rec if L == mn)
    assert k == len(K)
    print(dict(R))

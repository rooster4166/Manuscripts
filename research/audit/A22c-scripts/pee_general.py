"""Audit A22c: PEE failures for all connected all-odd simple G of order n (nauty-geng -c n) and all
3-matchings F (not up to automorphism), by the independent oracle.  Output lines in the format of
ptm_check.py ('PEEFAIL g6(G-F) a1 b1 a2 b2 a3 b3 short s1 s2 s3 simple=1') for thm_check.py.
usage: pee_general.py n [maxgraphs]"""
import sys, subprocess, itertools
from dlib import solve, check_decomp, check_constraints
from count_J import g6_decode, g6_encode


def main():
    n0 = int(sys.argv[1])
    p = subprocess.run(['nauty-geng', '-cq', str(n0)], capture_output=True, text=True, check=True)
    graphs = [l for l in p.stdout.split('\n') if l.strip()]
    cnt = dict(graphs=0, inst=0, ptm_fail=0, pee_tests=0, pee_fail=0)
    for s in graphs:
        n, A = g6_decode(s)
        if any(sum(r) % 2 == 0 for r in A):
            continue
        cnt['graphs'] += 1
        E = [(u, v) for v in range(n) for u in range(v) if A[u][v]]
        for F in itertools.combinations(E, 3):
            if len({x for e in F for x in e}) != 6:
                continue
            cnt['inst'] += 1
            fid = [E.index(f) for f in F]
            ends = set(range(n))
            D = solve(n, E, ends, spec={f: -1 for f in fid})
            if D is None:
                cnt['ptm_fail'] += 1
            B = [row[:] for row in A]
            for a, b in F:
                B[a][b] = B[b][a] = 0
            gp = g6_encode(n, B)
            for c in range(8):
                sh = [F[i][(c >> i) & 1] for i in range(3)]
                spec = {fid[i]: sh[i] for i in range(3)}
                cnt['pee_tests'] += 1
                D = solve(n, E, ends, spec=spec)
                if D is None:
                    cnt['pee_fail'] += 1
                    print('PEEFAIL', gp, ' '.join(f'{a} {b}' for a, b in F), 'short', *sh, 'simple=1', flush=True)
                else:
                    check_decomp(n, E, D, ends); check_constraints(D, spec=spec)
    print('SUMMARY', n0, ' '.join(f'{k}={v}' for k, v in cnt.items()), flush=True)


if __name__ == '__main__':
    main()

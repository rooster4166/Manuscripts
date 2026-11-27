"""Audit A22c: independent PTM_3 oracle on G = (J - z) + F, working on G directly (multigraph when a
pair of F is adjacent in J - z), with dsolve and an independent witness verifier.
usage: ptm_check.py FILE [pee] [simple] [start step]
  FILE: lines g6(J - z); every perfect matching F of the even vertices is an instance.
  Tests: PTM(G,F); PTM(G,F; e@x) for the 6 choices; with 'pee' also the 8 all-ends prescriptions,
  whose failures are written as 'PEEFAIL g6 a1 b1 a2 b2 a3 b3 short s1 s2 s3 simple=0/1'."""
import sys
from dlib import solve, check_decomp, check_constraints
from count_J import g6_decode, pairings


def instance(B, n, F):
    edges = [(u, v) for v in range(n) for u in range(v) if B[u][v]]
    fid = []
    for a, b in F:
        fid.append(len(edges)); edges.append((a, b))
    return edges, fid


def shorts_of(D, edges, fid):
    """for each F-edge, the set of its ends at which it is terminal in D"""
    res = []
    for f in fid:
        s = set()
        for vs, es in D:
            if es[0] == f: s.add(vs[0])
            if es[-1] == f: s.add(vs[-1])
        res.append(s)
    return res


def query(n, edges, ends, spec):
    D = solve(n, edges, ends, spec=spec)
    if D is not None:
        check_decomp(n, edges, D, ends)
        check_constraints(D, spec=spec)
    return D


def main():
    fn = sys.argv[1]
    pee = 'pee' in sys.argv[2:]
    simple_only = 'simple' in sys.argv[2:]
    nums = [int(a) for a in sys.argv[2:] if a.isdigit()]
    start, step = (nums[0], nums[1]) if len(nums) >= 2 else (0, 1)
    lines = [l.split()[0] for l in open(fn) if l.strip()]
    cnt = dict(inst=0, par=0, ptm_fail=0, r_tests=0, r_fail=0, pee_tests=0, pee_fail=0, pee_fail_simple=0)
    for idx in range(start, len(lines), step):
        s = lines[idx]
        n, B = g6_decode(s)
        deg = [sum(r) for r in B]
        ev = [v for v in range(n) if deg[v] % 2 == 0]
        for F in pairings(ev):
            simple = not any(B[a][b] for a, b in F)
            if simple_only and not simple:
                continue
            edges, fid = instance(B, n, F)
            ends = set(range(n))
            cnt['inst'] += 1; cnt['par'] += (not simple)
            D = query(n, edges, ends, {f: -1 for f in fid})
            if D is None:
                cnt['ptm_fail'] += 1; print('PTMFAIL', s, F, flush=True); continue
            known = shorts_of(D, edges, fid)
            for i, f in enumerate(fid):
                for x in F[i]:
                    cnt['r_tests'] += 1
                    if x in known[i]:
                        continue
                    spec = {g: -1 for g in fid}; spec[f] = x
                    D2 = query(n, edges, ends, spec)
                    if D2 is None:
                        cnt['r_fail'] += 1; print('RFAIL', s, F, f, x, flush=True)
                    else:
                        for j, t in enumerate(shorts_of(D2, edges, fid)):
                            known[j] |= t
            if pee:
                for c in range(8):
                    sh = [F[i][(c >> i) & 1] for i in range(3)]
                    spec = {fid[i]: sh[i] for i in range(3)}
                    cnt['pee_tests'] += 1
                    if query(n, edges, ends, spec) is None:
                        cnt['pee_fail'] += 1; cnt['pee_fail_simple'] += simple
                        print('PEEFAIL', s, ' '.join(f'{a} {b}' for a, b in F), 'short', *sh, f'simple={int(simple)}', flush=True)
    print('SUMMARY', ' '.join(f'{k}={v}' for k, v in cnt.items()), flush=True)


if __name__ == '__main__':
    main()

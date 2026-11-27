"""Audit A22c: re-derive the walk3 reach table (Section 8) with chain.py + dsolve, and compare the
set of base configurations with walk3's BASE lines.
usage: reach.py G6FILE MODE [WALK3_ALL_OUT] [flag=1 ...] [start step]
  G6FILE: lines g6(J - z); simple pairings of the even vertices are the instances.
  MODE: walk3 (shortest semantics of walk3.c) or all (chains of every length).
Prints per-order summary and the per-J coverage histogram (r covered = r is some y_i of a
configuration with a base)."""
import sys, collections
from count_J import g6_decode, pairings
from chain import FLAGS, configs, chains, has_walks, base_test


def main():
    fn, mode = sys.argv[1], sys.argv[2]
    cmp = None
    fl = dict(FLAGS)
    nums = []
    for a in sys.argv[3:]:
        if '=' in a:
            k, v = a.split('='); assert k in fl; fl[k] = bool(int(v))
        elif a.isdigit():
            nums.append(int(a))
        else:
            cmp = a
    start, step = (nums[0], nums[1]) if len(nums) >= 2 else (0, 1)
    lines = [l.split()[0] for l in open(fn) if l.strip()]
    inst = base_ok = nopath = nochain = 0
    tried = 0
    bases = set()
    hist = collections.Counter()
    for idx in range(start, len(lines), step):
        s = lines[idx]
        n, B = g6_decode(s)
        deg = [sum(r) for r in B]
        ev = [v for v in range(n) if deg[v] % 2 == 0]
        E0 = {frozenset((u, v)) for v in range(n) for u in range(v) if B[u][v]}
        cov = set()
        for F in pairings(ev):
            if any(B[a][b] for a, b in F):
                continue
            inst += 1
            E = E0 | {frozenset(p) for p in F}
            anyw = anych = anyb = False
            for X, Y in configs(F):
                if has_walks(n, E, X, Y, fl):
                    anyw = True
                found = False
                for P2, P1 in chains(n, E, X, Y, fl, mode):
                    anych = True
                    tried += 1
                    D, _ = base_test(n, E, X, Y, P2, P1)
                    if D is not None:
                        found = True; break
                if found:
                    anyb = True
                    bases.add((s, frozenset(frozenset(p) for p in F), X))
                    cov |= set(Y)
            base_ok += anyb; nopath += (not anyw); nochain += (not anych)
        hist[len(cov)] += 1
    print(f'{fn.split("/")[-1]} mode={mode} flags={ {k: v for k, v in fl.items() if v} } inst={inst} base_ok={base_ok} '
          f'no_walk_pair={nopath} no_edge_disjoint_chain={nochain} base_configs={len(bases)} tried={tried}')
    print('  J coverage histogram (covered r per J):', dict(sorted(hist.items())))
    if cmp:
        theirs = set()
        for line in open(cmp):
            if line.startswith('BASE'):
                t = line.split()
                F = [(int(t[2]), int(t[3])), (int(t[4]), int(t[5])), (int(t[6]), int(t[7]))]
                theirs.add((t[1], frozenset(frozenset(p) for p in F), (int(t[9]), int(t[10]), int(t[11]))))
        if step != 1:
            keep = {lines[i] for i in range(start, len(lines), step)}
            theirs = {k for k in theirs if k[0] in keep}
        print(f'  compare with {cmp.split("/")[-1]}: theirs {len(theirs)}, mine {len(bases)}, '
              f'only theirs {len(theirs - bases)}, only mine {len(bases - theirs)}')
        for k in list(theirs - bases)[:5]: print('   only theirs', k)
        for k in list(bases - theirs)[:5]: print('   only mine', k)


if __name__ == '__main__':
    main()

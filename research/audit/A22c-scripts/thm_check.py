"""Audit A22c: adversarial test of Theorem 8.2.  The conclusion of the theorem for a configuration
(x_i short) is exactly PEE with short ends x1, x2, x3 (each x_i y_i terminal at x_i, three different
paths).  So a counterexample is a PEE failure (G, F, shorts) with an admissible chain whose base
graph has the separating decomposition.  For every PEE failure we try all 6 orders of the three
edges (orientation fixed by the shorts) and every admissible chain of every length, for the literal
Definition 8.1 and for relaxed variants (one condition dropped at a time).
usage: thm_check.py PEEFAIL_LOG [maxlen]
  PEEFAIL lines: 'PEEFAIL g6 a1 b1 a2 b2 a3 b3 short s1 s2 s3 simple=1' (G' = G - F given by g6)."""
import sys, itertools, collections
from count_J import g6_decode
from chain import FLAGS, chains, base_test

VARIANTS = ['strict', 'nbrH', 'allow_y1', 'no_y2x3', 'no_P1N2', 'no_P1N3', 'no_P2N3', 'allow_x1_P2', 'allow_y2_P2']


def main():
    fn = sys.argv[1]
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else None
    fails = []
    for line in open(fn):
        if not line.startswith('PEEFAIL') or 'simple=1' not in line:
            continue
        t = line.split()
        F = [(int(t[2]), int(t[3])), (int(t[4]), int(t[5])), (int(t[6]), int(t[7]))]
        sh = (int(t[9]), int(t[10]), int(t[11]))
        fails.append((t[1], F, sh))
    keys = {(s, frozenset(sh)) for s, F, sh in fails}
    print(f'{fn}: {len(fails)} simple PEE failures, {len(keys)} distinct (graph, short set) keys')
    res = collections.Counter(); chains_tried = collections.Counter(); example = {}
    for s, F, sh in fails:
        n, B = g6_decode(s)
        E = {frozenset((u, v)) for v in range(n) for u in range(v) if B[u][v]} | {frozenset(p) for p in F}
        long_ = [a if b == x else b for (a, b), x in zip(F, sh)]
        for var in VARIANTS:
            fl = dict(FLAGS)
            if var != 'strict':
                fl[var] = True
            hit = False
            for perm in itertools.permutations(range(3)):
                X = tuple(sh[i] for i in perm); Y = tuple(long_[i] for i in perm)
                for P2, P1 in chains(n, E, X, Y, fl, mode='all', maxlen=maxlen):
                    chains_tried[var] += 1
                    try:
                        D, el = base_test(n, E, X, Y, P2, P1)
                    except AssertionError:
                        continue          # parity broken by the relaxation: not a base graph
                    if D is not None:
                        hit = True
                        example.setdefault(var, (s, F, X, Y, P2, P1))
                        break
                if hit:
                    break
            res[var] += hit
    for var in VARIANTS:
        print(f'  {var:12s}: PEE failures with a base (counterexamples to this form) = {res[var]:4d}  (chains tried {chains_tried[var]})')
        if var in example:
            print('     e.g.', example[var])


if __name__ == '__main__':
    main()

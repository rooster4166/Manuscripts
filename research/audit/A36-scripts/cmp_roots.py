"""cmp_roots.py (A36): compare per-root verdicts of indep_mt (R lines) with the authors' mtok run
(ROOT lines).  Verdicts 1 = schedule, 0 = none (exhaustive), 2 = undecided (budget / state cap).
A conflict is 1 vs 0 or 0 vs 1; 2 against anything is a budget difference, not a conflict.
usage: cmp_roots.py AUTHORS_RUN.txt MINE.txt [MINE2.txt ...]"""
import sys
from collections import Counter
theirs = {}
for l in open(sys.argv[1]):
    if l.startswith('ROOT'):
        p = l.split(); theirs[(p[1], int(p[2][2:]))] = int(p[3][8:])
mine = {}
for f in sys.argv[2:]:
    for l in open(f):
        if l.startswith('R '):
            p = l.split(); mine[(p[1], int(p[2]))] = int(p[5])
c = Counter((theirs[k], mine[k]) for k in mine)
print('roots compared', len(mine), ' (authors, A36) ->', dict(sorted(c.items())))
print('conflicts (1 vs 0 or 0 vs 1):', c[(1, 0)] + c[(0, 1)])

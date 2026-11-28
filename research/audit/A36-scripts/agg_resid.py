"""agg_resid.py (A36): aggregate indep_mt R-lines: Prop 6.1 check and the frozen/partial table.
usage: agg_resid.py K(pairs) < indep_mt output"""
import sys
from collections import Counter
k = int(sys.argv[1])
rows = [l.split() for l in sys.stdin if l.startswith('R ')]
viol = [r for r in rows if int(r[4]) < k and r[5] != '0']
print('roots', len(rows), 'roots with < k non-neighbours', sum(1 for r in rows if int(r[4]) < k),
      'Prop 6.1 violations', len(viol))
uns = [r for r in rows if r[5] == '0']
und = [r for r in rows if r[5] == '2']
print('unscheduled (none)', len(uns), 'undecided', len(und))
nm2 = [r for r in uns if int(r[4]) < k]
oth = [r for r in uns if int(r[4]) >= k]
print('  with < k non-neighbours', len(nm2), ' of which frozen (min phi 5)', sum(1 for r in nm2 if r[10] == '5'),
      ' minphi dist', sorted(Counter(r[10] for r in nm2).items()))
print('  other', len(oth), ' minphi dist', sorted(Counter(r[10] for r in oth).items()))
print('  other by degree', sorted(Counter(int(r[3]) for r in oth).items()))
print('  other frozen by #non-neighbours', sorted(Counter(int(r[4]) for r in oth if r[10] == '5').items()))
print('  all unscheduled by #non-neighbours', sorted(Counter(int(r[4]) for r in uns).items()))
print('  scheduled by #non-neighbours', sorted(Counter(int(r[4]) for r in rows if r[5] == '1').items()))

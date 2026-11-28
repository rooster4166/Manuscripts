"""b_core.py -- minimal failing subfamily (deletion-minimal) of a non-sparse leaf-tail instance.
usage: python3 b_core.py 'g6 A t a A t a ...'"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a40lib import dec, solve_lines
t = sys.argv[1].split(); g = t[0]
cons = [(int(t[i + 1]), int(t[i + 2])) for i in range(1, len(t), 3)]
def sat(cs):
    return solve_lines([g + ''.join(' A %d %d' % c for c in cs)])[0][0] == 'SAT'
assert not sat(cons)
core = list(cons)
for c in list(core):
    trial = [x for x in core if x != c]
    if not sat(trial):
        core = trial
n, A = dec(g)
print(g, 'adj', [sorted(a) for a in A], 'minimal failing family', core)

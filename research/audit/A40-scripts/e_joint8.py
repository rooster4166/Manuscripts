"""e_joint8.py -- reproduce the 'joint decomposition Q(c1)=Q(c2) avoiding a1,a2 (exact)' row of the
ln.tex coverage table at order 8 with the audit's solver.  Every SAT witness is checked; UNDEC
answers are re-decided by path splitting (a_jsplit.py)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a40lib import dec, check, solve_lines
inst = [l.split() for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'inst8.txt'))]
qs = ['%s J %s %s A %s %s A %s %s' % (t[0], t[1], t[3], t[1], t[2], t[1], t[4]) for t in inst]
res = solve_lines(qs, budget=20000000)
st = {}
for t, (ans, W) in zip(inst, res):
    st[ans] = st.get(ans, 0) + 1
    if ans == 'SAT':
        n, A = dec(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
        assert check(n, A, W, [1] * n, [(c1, a1), (c1, a2), (c2, a1), (c2, a2)], (), [(c1, c2)]) is None
    elif ans == 'UNDEC':
        print('UNDEC', ' '.join(t))
print('instances', len(inst), st)

"""b_mtl2count.py -- reproduce the MTL2 instance counts of ln.tex Sec. 7 with own code, and decide them
with trsolve.  usage: nauty-geng -cq n | python3 b_mtl2count.py ts|nots
ts  : leaves c1 < c2, w1 != c2; x_i not in {c_i, w_i} u N(w_i); x_i odd; x1 not in {c2, w2};
      x2 not in {c1, w1}; x1 != x2   (the static conditions (TS) of multi-token, x odd)
nots: leaves c1 < c2, w1 != c2; x_i not in {c_i, w_i} u N(w_i)  (x_i may be even, x1 = x2 allowed)
notsodd: as nots, but x_i odd"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a40lib import dec, check, solve_lines
mode = sys.argv[1]
jobs = []
for g in sys.stdin:
    g = g.strip()
    if not g: continue
    n, A = dec(g); d = [len(a) for a in A]
    if sum(1 for v in range(n) if d[v] > 0 and d[v] % 2 == 0) > 1: continue
    L = [v for v in range(n) if d[v] == 1]
    for i, c1 in enumerate(L):
        (w1,) = A[c1]
        for c2 in L[i + 1:]:
            (w2,) = A[c2]
            if w1 == c2: continue
            for x1 in range(n):
                if x1 in (c1, w1) or x1 in A[w1]: continue
                if mode == 'ts' and (d[x1] % 2 == 0 or x1 in (c2, w2)): continue
                if mode == 'notsodd' and d[x1] % 2 == 0: continue
                for x2 in range(n):
                    if x2 in (c2, w2) or x2 in A[w2]: continue
                    if mode == 'ts' and (d[x2] % 2 == 0 or x2 in (c1, w1) or x2 == x1): continue
                    if mode == 'notsodd' and d[x2] % 2 == 0: continue
                    jobs.append((g + ' S %d %d S %d %d' % (c1, x1, c2, x2), n, A, [(c1, x1), (c2, x2)]))
res = solve_lines([j[0] for j in jobs], budget=1000000000) if jobs else []
st = {}
for (q, n, A, sp), (ans, W) in zip(jobs, res):
    st[ans] = st.get(ans, 0) + 1
    if ans == 'SAT':
        assert check(n, A, W, None, (), sp) is None, q
    else:
        print(ans, q)
print('instances', len(jobs), st, flush=True)

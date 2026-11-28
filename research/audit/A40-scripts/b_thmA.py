"""b_thmA.py -- (b) exhaustive test of Theorem A (and of its non-sparse variants) with the audit's
own generator and solver.

usage: nauty-geng -q n | python3 b_thmA.py [mode]
For every graph with at most one vertex of positive even degree and at least one leaf:
  mode 'sparse' (default): for every MAXIMAL sparse subset X of C = union of far(c) over the leaves c,
      the hardest family with heads in X (A_c = X & far(c) for every leaf c).  Every family of leaf
      tails with sparse heads is dominated by one of these, so this is exhaustive for Theorem A.
  mode 'full': the single family A_c = far(c) for every leaf c (no sparseness).
  mode 'fullnoleaf': A_c = far(c) minus the leaves (no sparseness, no tail avoids a leaf).
  mode 'mtl2': two tails, one head each, no sparseness: every pair of leaves c1 != c2 and every
      x1 in far(c1), x2 in far(c2); also c1 == c2 with two heads (a single tail with two heads).
far(c) = vertices at distance >= 3 from c.  Prints a summary line and every UNSAT/UNDEC instance."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a40lib import dec, check, solve_lines

mode = sys.argv[1] if len(sys.argv) > 1 else 'sparse'


def far(n, A, c):
    near = {c} | A[c]
    for w in A[c]:
        near |= A[w]
    return [v for v in range(n) if v not in near]


def sparse(A, X):
    return all(len(A[v] & X) <= 1 for v in range(len(A)))


def maximal_sparse(n, A, C):
    """all maximal sparse subsets of C (simple branch: include/exclude, then filter maximal)."""
    C = sorted(C)
    res = []
    def rec(i, X):
        if i == len(C):
            # maximal: no element of C - X can be added
            if all(not sparse(A, X | {y}) for y in C if y not in X):
                res.append(frozenset(X))
            return
        y = C[i]
        if sparse(A, X | {y}):
            rec(i + 1, X | {y})
        rec(i + 1, X)
    rec(0, frozenset())
    return res


jobs = []   # (line, n, A, avoid list, label)
ngraphs = 0
for g in sys.stdin:
    g = g.strip()
    if not g:
        continue
    n, A = dec(g)
    d = [len(a) for a in A]
    if sum(1 for v in range(n) if d[v] > 0 and d[v] % 2 == 0) > 1:
        continue
    leaves = [v for v in range(n) if d[v] == 1]
    if not leaves:
        continue
    ngraphs += 1
    F = {c: far(n, A, c) for c in leaves}
    if mode == 'sparse':
        C = set().union(*[set(F[c]) for c in leaves])
        for X in maximal_sparse(n, A, C):
            av = [(c, a) for c in leaves for a in F[c] if a in X]
            if av:
                jobs.append((g + ''.join(' A %d %d' % x for x in av), n, A, av, 'X=%s' % sorted(X)))
    elif mode in ('full', 'fullnoleaf'):
        av = [(c, a) for c in leaves for a in F[c] if mode == 'full' or a not in leaves]
        if av:
            jobs.append((g + ''.join(' A %d %d' % x for x in av), n, A, av, mode))
    elif mode == 'mtl2':
        for i, c1 in enumerate(leaves):
            for c2 in leaves[i:]:
                for x1 in F[c1]:
                    for x2 in F[c2]:
                        if c1 == c2 and x2 <= x1:
                            continue
                        av = [(c1, x1), (c2, x2)]
                        jobs.append((g + ' A %d %d A %d %d' % (c1, x1, c2, x2), n, A, av,
                                     'same-leaf' if c1 == c2 else 'two-leaves'))

res = solve_lines([j[0] for j in jobs], budget=500000000) if jobs else []
stat = {}
for (line, n, A, av, lab), (ans, W) in zip(jobs, res):
    key = (lab if mode == 'mtl2' else mode, ans)
    stat[key] = stat.get(key, 0) + 1
    if ans == 'SAT':
        err = check(n, A, W, None, av)
        if err:
            print('BADWIT', line, err)
    else:
        print(ans, line, lab)
print('graphs', ngraphs, 'instances', len(jobs), 'results', stat, flush=True)

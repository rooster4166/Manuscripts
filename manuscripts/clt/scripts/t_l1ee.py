"""t_l1ee.py: L1* local form at c together with EE at a neighbour x of the even vertex g.
For every graph (graph6 on stdin) with exactly one even vertex g, every odd c, A = V - (N[c] u N(g))
(non-isolated), and every x in N(g) - {c}: is there a Lovász decomposition with Q_c disjoint from A
and xg terminal at x?  Prints per-graph failures and totals; 'some x' = existential over x."""
import sys
from clt_lib import parse_g6, solve_many, even_vertices, check
tot = fail = ex_fail = inst = 0
for line in sys.stdin:
    g6 = line.strip()
    n, adj = parse_g6(g6)
    ev = even_vertices(n, adj)
    if len(ev) != 1:
        continue
    g = ev[0]
    items, meta = [], []
    for c in range(n):
        if len(adj[c]) % 2 == 0:
            continue
        A = {a for a in range(n) if adj[a] and a != c and a not in adj[c] and a not in adj[g]}
        for x in sorted(adj[g]):
            if x == c:
                continue
            S = set(range(n)) - {x}
            items.append((n, adj, {'ef': {c: A}, 'es': [(x, g, S)]}))
            meta.append((c, x))
    if not items:
        continue
    res = solve_many(items)
    per_c = {}
    for (c, x), (st, P), it in zip(meta, res, items):
        inst += 1
        ok = st == 'OK'
        if ok:
            assert check(n, adj, P, it[2])
        else:
            fail += 1
            print('FAIL', g6, 'g', g, 'c', c, 'x', x, st)
        per_c.setdefault(c, []).append(ok)
    for c, L in per_c.items():
        if not any(L):
            ex_fail += 1
            print('EXFAIL', g6, 'g', g, 'c', c)
print(f'instances {inst} failures {fail} (c with no good x: {ex_fail})')

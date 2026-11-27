"""t6all.py: the t6 append base for EVERY labelling (session claude/clt).
For each B (graph6, U = {0..5}) and every labelling with x1y2, x2y3 in E(B): exact DFS with a small
budget, then local search (lsls.py) on undecided instances.  Counts: found / proved none / unknown.
usage: t6all.py BUDGET STEPS < B.g6"""
import sys, itertools
from clt_lib import parse_g6, solve_many, check
from t6probe import base_graph, system
from lsls import search
budget = int(sys.argv[1]); steps = int(sys.argv[2])
for line in sys.stdin:
    g6 = line.strip()
    if not g6:
        continue
    nB, adjB = parse_g6(g6)
    Ls = [p for p in itertools.permutations(range(6)) if p[3] in adjB[p[0]] and p[5] in adjB[p[2]]]
    items = []
    for L in Ls:
        n, adj, z = base_graph(nB, adjB, L)
        items.append((n, adj, system(L, z)))
    res = solve_many(items, budget=budget)
    found = none = unk = 0
    for L, it, (st, P) in zip(Ls, items, res):
        if st == 'OK':
            assert check(it[0], it[1], P, it[2]); found += 1
        elif st == 'NONE':
            none += 1; print('NONE', g6, L, flush=True)
        else:
            P = search(it[0], it[1], it[2], steps=steps, k=3, seed=1)
            if P:
                found += 1
            else:
                unk += 1; print('UNKNOWN', g6, L, flush=True)
    print(g6, f'labellings {len(Ls)} found {found} none {none} unknown {unk}', flush=True)

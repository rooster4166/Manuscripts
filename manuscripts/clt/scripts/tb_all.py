"""tb_all.py: the triangle base for EVERY root, data choice and orientation (session claude/clt).
B graph6 on stdin (U = N(z) = {0..5}, z joined to U).  Counts per graph: instances (root, w, M0,
orientation) with a base found (exact DFS budget 2*10^4, then local search), proved absent, unknown.
usage: tb_all.py < B.g6"""
import sys, itertools
from clt_lib import parse_g6, solve_many, check
from lsls import search
from tb_ls import pms
for line in sys.stdin:
    g6 = line.strip()
    if not g6:
        continue
    nB, adjB = parse_g6(g6)
    n = nB + 1; z = nB
    adj = [set(a) for a in adjB] + [set()]
    for u in range(6):
        adj[z].add(u); adj[u].add(z)
    found = none = unk = 0
    for r in range(6):
        for w in range(6):
            if w == r:
                continue
            for pm in pms([u for u in range(6) if u not in (r, w)], adj):
                M = [set(a) for a in adj]
                for a, b in [(z, w)] + [(z, a) for a, _ in pm] + [(z, b) for _, b in pm] + pm:
                    M[a].discard(b); M[b].discard(a)
                for orient in itertools.product((0, 1), repeat=len(pm)):
                    ef = {}
                    for (a, b), o in zip(pm, orient):
                        c, x = (a, b) if o == 0 else (b, a)
                        ef.setdefault(c, set()).add(x)
                    sysd = {'ef': ef}
                    st, P = solve_many([(n, M, sysd)], budget=20000)[0]
                    if st == 'NONE':
                        none += 1; print('NONE', g6, r, w, pm, orient, flush=True); continue
                    if st != 'OK':
                        P = search(n, M, sysd, steps=3000, k=3, seed=1)
                    if P:
                        assert check(n, M, P, sysd); found += 1
                    else:
                        unk += 1; print('UNKNOWN', g6, r, w, pm, orient, flush=True)
    print(g6, f'instances {found + none + unk} found {found} none {none} unknown {unk}', flush=True)

#!/usr/bin/env python3
"""Audit A43: is TW2 (Lemma 5.8) ever needed?  Counts PC instances (two zeros, (DB)) where the
TW2 hypotheses hold, and among them those where SUP (Lemma 5.3) does not apply.  stdin: geng -C."""
import sys
from itertools import combinations
src = open(__file__.rsplit('/', 1)[0] + '/a43_irred.py').read().split('def main')[0]
exec(src)
tw2 = tw2_nosup = 0
for line in sys.stdin:
    s = line.strip(); n, adj = g6(s); deg = [len(a) for a in adj]
    if all(d == 2 for d in deg):
        continue
    ths = threads(n, adj)
    ev = [x for x in range(n) if deg[x] % 2 == 0]
    for Z in combinations(ev, 2):
        u, v = Z
        if v in adj[u] or adj[u] != adj[v] or len(adj[u]) != 2:
            continue
        x, y = sorted(adj[u])
        if y in adj[x]:
            continue
        a2 = [t - {u, v} for t in adj]; a2[u] = set(); a2[v] = set(); a2[x].add(y); a2[y].add(x)
        W = set(range(n)) - {u, v}
        choices = [[0] if i in Z else list(range(1 if deg[i] % 2 else 2, deg[i] + 1, 2)) for i in range(n)]
        profs = [[]]
        for c in choices:
            profs = [p + [w] for p in profs for w in c]
        for b in profs:
            if not db_ok(set(range(n)), adj, b):
                continue
            b2 = list(b); b2[x] -= 1; b2[y] -= 1
            if not (twoconn(W, a2) and sum(1 for w in W if b2[w] == 0) <= 2 and db_ok(W, a2, b2)):
                continue
            tw2 += 1
            sup = any(len(P) > 2 and all(z in Z for z in P[1:-1]) and len(P) <= 4 and P[-1] not in adj[P[0]] for P in ths)
            if not sup:
                tw2_nosup += 1
print('TW2 applicable', tw2, 'of which SUP not applicable', tw2_nosup)

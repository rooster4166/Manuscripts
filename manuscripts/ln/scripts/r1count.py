"""Criterion R with P restricted to a single edge (search only): count instances covered."""
import sys
from routeR import find
from lnlib import g6_decode
tot = ok = 0
for line in sys.stdin:
    t = line.split()
    if not t: continue
    n, adj = g6_decode(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
    tot += 1
    if find(n, adj, c1, a1, c2, a2, maxlen=1) is not None: ok += 1
    else: print('NOR1', line.strip(), flush=True)
print('total', tot, 'covered with |P| = 1', ok, file=sys.stderr)

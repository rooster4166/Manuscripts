"""A29: test the 'local degree-two reason' of dl-one Sec. 10.4 on the 118 full-separation failures.
usage: ./dl -m sep1 < oe57.g6 > sep1.out ; python3 sep1_reason.py sep1.out   (needs dllib.py on sys.path)"""
import sys
from collections import Counter
from dllib import g6_decode, adjsets, degrees
C = Counter()
for line in open(sys.argv[1]):
    if not line.startswith('SEP1'):
        continue
    f = line.split(); g6 = f[1]; kv = dict(x.split('=') for x in f[2:])
    a, b, w, g, sep = (int(kv[k]) for k in ('a', 'b', 'w', 'g', 'sep'))
    n, E = g6_decode(g6); A = adjsets(n, E); d = degrees(n, E)
    if d[a] < 3 or d[b] < 3:
        continue
    C['instances'] += 1; C['separable'] += sep
    deg2 = [v for v in range(n) if d[v] == 2]
    if any(A[v] == {a, b} for v in deg2) or any(A[v] in ({b, w}, {a, w}) for v in deg2):
        C['stated reason applies'] += 1
    if d[g] >= 4:
        C['no degree-2 vertex at all (d(g)>=4)'] += 1
print(dict(C))

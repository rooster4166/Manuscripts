"""summarize_routeR.py FILE -- breakdown of routeR.py output: route (joint / pre), length of P, moves."""
import sys, collections
kinds = collections.Counter(); plen = collections.Counter(); mv = collections.Counter(); bad = 0; tot = 0
for line in open(sys.argv[1]):
    t = line.split()
    if not t: continue
    tot += 1
    if t[0] != 'OK': bad += 1; continue
    kinds[t[1]] += 1
    P = [x for x in t if x.startswith('P=')][0][2:].split('-')
    plen[len(P) - 1] += 1
    mv[int([x for x in t if x.startswith('moves=')][0][6:])] += 1
print('instances', tot, 'not certified', bad)
print('route', dict(kinds))
print('edges of P', dict(sorted(plen.items())))
print('moves', dict(sorted(mv.items())))

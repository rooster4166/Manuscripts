"""A30 audit: independent recount of Section 6 / Section 7 numbers from the per-root tables.
Usage: python3 recount.py DATA_OUT_DIR
Own implementation of the counting bound CB (Prop 4.1), written from the manuscript text."""
import gzip, sys, os, math
from collections import Counter
import networkx as nx

def CB(degs, dr):
    p = 1
    while True:
        c = [min(d, 2*p - d) for d in degs]
        if min(dr, 2*p - dr) >= 2 and min(c) >= 0 and sum(c) >= 2*p:
            return p
        p += 1

out = sys.argv[1]
cache = {}
def info(g6):
    if g6 not in cache:
        B = nx.from_graph6_bytes(g6.encode())
        cache[g6] = (B, [d for _, d in B.degree()], nx.is_biconnected(B))
    return cache[g6]

res = Counter(); ucv = []
for n in range(3, 11):
    fns = ['reconn_%d.tab.gz' % n] if n < 10 else ['re_10_min.tab.gz', 'reconn_10_not2c.tab.gz']
    for fn in fns:
        for line in gzip.open(os.path.join(out, fn), 'rt'):
            g6, r, p, k, st = line.split(); r, p = int(r), int(p)
            B, degs, bic = info(g6)
            assert B.number_of_nodes() == n
            key = (n, '2c' if bic else 'c')
            if st == 'UNK':
                res[key + ('UNK',)] += 1; continue
            c = CB(degs, degs[r])
            assert p >= c, (g6, r, p, c)
            ce = (n + 1) // 2
            res[key + ('roots',)] += 1
            res[key + ('RE*ok' if p <= ce else 'RE*FAIL',)] += 1
            if p > max(c, ce - 1):
                res[key + ('UCFAIL',)] += 1; ucv.append((g6, r, p, c, n))
for k in sorted(res): print(*k, res[k])
print('UC violations', len(ucv))
for v in ucv: print(*v)

"""A41: compare the auditor's from-scratch tiers on the systematic order-11 sample with the authors'
data.  Authors: a root is tier >= 2 iff it is in data/nd_t1_11_ge2.txt.gz (with its level);
otherwise it is tier 1.  Auditor: a41 tiers with A41_MAXTIER=2 ('tier 3' means 'tier >= 3').
usage: python3 -I cmp_sample11.py sample11_tiers.txt nd_t1_11_ge2.txt.gz"""
import gzip
import sys
from collections import Counter

ge2 = {}
for l in gzip.open(sys.argv[2], "rt"):
    if not l.startswith("ND "):
        continue
    g = l.split()[1]
    f = l[3 + len(g):].split("|")[0].split()
    ge2[(g, f[0], f[1])] = int(f[13])
c = Counter()
for l in open(sys.argv[1]):
    f = l.split()
    if not f or f[0] != "T1":
        continue
    k = (f[1], f[2], f[3])
    mine = int(f[9])
    auth = ge2.get(k, 1)
    auth = min(auth, 3)
    c[(auth, mine)] += 1
print("(authors' tier, auditor's tier) counts:", sorted(c.items()))
print("roots", sum(c.values()), "agree", sum(v for (a, b), v in c.items() if a == b))

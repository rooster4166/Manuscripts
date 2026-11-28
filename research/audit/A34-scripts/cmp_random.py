#!/usr/bin/env python3
"""cmp_random.py (audit A34): compare per-graph TRN test counts of indep9 (rper/*.txt) with the
authors' trnbud (trnbud_per.txt) on the random order-11/13 graphs."""
import sys, os, re
S = sys.argv[1]
tb = {}
for line in open(os.path.join(S, 'trnbud_per.txt')):
    h, rest = line.split(' ', 1)
    m = re.search(r'TRN tests=(\d+) viol=(\d+) undecided=(\d+) \(child undecided (\d+)\); TRN-E holds (\d+), undecided (\d+)', rest)
    tb[h] = tuple(map(int, m.groups()))
eq = diff = n = 0; extra = 0; tot_tb = tot_me = 0; tout = []
for f in os.listdir(os.path.join(S, 'rper')):
    h = f[:-4]; txt = open(os.path.join(S, 'rper', f)).read()
    if 'TIMEOUT' in txt: tout.append((txt.split()[1], tb.get(h))); continue
    m = re.search(r'TRN tests y!~g=(\d+) y~g=(\d+); TRN_E holds y!~g=(\d+) y~g=(\d+); TRN violations=(\d+)', txt)
    me = int(m.group(1)) + int(m.group(2)); n += 1
    t = tb[h]; tot_tb += t[0]; tot_me += me
    # authors' count excludes child-undecided candidates: mine must equal t[0] + (good children among them)
    if me == t[0]: eq += 1
    elif t[0] < me <= t[0] + t[3]: extra += 1
    else: diff += 1; print('MISMATCH', h, me, t)
print(f'{n} graphs decided by indep9: test counts equal {eq}, larger only by child-undecided {extra}, mismatches {diff}; totals indep9 {tot_me} vs trnbud {tot_tb}')
print('timed out (30 s) in indep9:', tout)
print('trnbud totals over all 400:', [sum(v[i] for v in tb.values()) for i in range(6)])

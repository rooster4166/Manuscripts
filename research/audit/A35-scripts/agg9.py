#!/usr/bin/env python3
"""agg9.py (audit A35): aggregate data/classify9_first4000.txt (classify.cpp output, 4 parts)
independently of summarize.py, including the hard-core split of Section 9 (hard core = i=1 and
u not in Q'(y)).  usage: python3 -I agg9.py classify9_first4000.txt"""
import sys, re, collections
T = collections.Counter()
for line in open(sys.argv[1]):
    if line.startswith('SUMMARY'):
        m = re.search(r'tests=(\d+) \(skipped (\d+) .*instances-with-bad-D\'=(\d+) bad D\'=(\d+) all-repairs-fail=(\d+)', line)
        t, s, ib, b, f = map(int, m.groups())
        T['S_tests'] += t; T['S_skipped'] += s; T['S_inst_bad'] += ib; T['S_bad'] += b; T['S_allfail'] += f
        continue
    m = re.match(r'\s+adj=(\d) i=(\S+) side=(\w) qu=(\d) wit=(\d) tri2=(\d) \| exch=(\d) rot=(\d) rep=(\d) loc=(\d)\s+(\d+)\s*$', line)
    if not m: continue
    adj, i, side, qu, wit, tri2, exch, rot, rep, loc, c = m.groups(); c = int(c)
    hard = 'H' if (i == '1' and qu == '0') else 'O'
    fixed = '1' in (exch, rot, rep, loc)
    for k in ('all', hard):
        T[k + '_bad'] += c
        T[k + '_fixed'] += c * fixed
        T[k + '_loc'] += c * (loc == '1')
        if not fixed:
            T[k + '_none'] += c
            T[k + '_none_qu' + qu] += c
            T[k + '_none_i' + i] += c
for k in sorted(T): print(f'{k:24s} {T[k]:>14,}')

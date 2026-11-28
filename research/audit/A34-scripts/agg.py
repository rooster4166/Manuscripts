#!/usr/bin/env python3
"""agg.py: aggregate indep.cpp classification lines (audit A34)."""
import sys, re, collections
T = collections.Counter()
for line in open(sys.argv[1]):
    m = re.match(r'\s+adj=(\d) i=(\S+) side=(\w) qu=(\d) wit=(\d) tri2=(\d) gwit=(\d) hard=(\d) \| exch=(\d) rot=(\d) rep=(\d) loc=(\d)\s+(\d+)', line)
    if not m: continue
    adj, i, side, qu, wit, tri2, gwit, hard, exch, rot, rep, loc, c = m.groups(); c = int(c)
    fixed = '1' in (exch, rot, rep, loc)
    T['bad'] += c; T['adj'+adj] += c; T['i'+i] += c; T['side'+side] += c; T['qu'+qu] += c
    for k, v in (('exch', exch), ('rot', rot), ('rep', rep), ('loc', loc)): T[k] += c * (v == '1')
    T['fixed'] += c * fixed
    T['hard'+hard] += c; T['hard%s_loc%s' % (hard, loc)] += c
    if not fixed:
        T['none'] += c
        for k, v in (('adj', adj), ('i', i), ('qu', qu), ('side', side), ('tri2', tri2), ('wit', wit), ('gwit', gwit), ('hard', hard)):
            T['none_%s%s' % (k, v)] += c
    if loc == '0' and fixed: T['fixed_without_loc'] += c; T['fixed_without_loc_rep%s_rot%s_exch%s' % (rep, rot, exch)] += c
    if gwit == '1': T['gwit_bad'] += c
for k in sorted(T): print(f'{k:40s} {T[k]}')

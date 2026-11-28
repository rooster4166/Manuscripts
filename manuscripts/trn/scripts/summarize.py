#!/usr/bin/env python3
"""summarize.py: aggregate a classify.cpp output into the tables of the manuscript.
usage: python3 summarize.py classify_output.txt"""
import sys, re, collections
tot = collections.Counter()
for line in open(sys.argv[1]):
    m = re.match(r'\s+adj=(\d) i=(\S+) side=(\w) qu=(\d) wit=(\d) tri2=(\d) \| exch=(\d) rot=(\d) rep=(\d) loc=(\d)\s+(\d+)', line)
    if not m: continue
    adj, i, side, qu, wit, tri2, exch, rot, rep, loc, c = m.groups(); c = int(c)
    fixed = exch == '1' or rot == '1' or rep == '1' or loc == '1'
    tot['bad'] += c
    tot['adj' + adj] += c
    tot['i' + i] += c
    tot['side' + side] += c
    tot['qu' + qu] += c
    tot['exch'] += c * (exch == '1'); tot['rot'] += c * (rot == '1'); tot['rep'] += c * (rep == '1'); tot['loc'] += c * (loc == '1')
    tot['fixed'] += c * fixed
    if not fixed:
        tot['unfixed'] += c
        tot['unfixed_adj' + adj] += c; tot['unfixed_i' + i] += c; tot['unfixed_qu' + qu] += c
        tot['unfixed_side' + side] += c; tot['unfixed_tri2_' + tri2] += c; tot['unfixed_wit' + wit] += c
for line in open(sys.argv[1]):
    if line.startswith('SUMMARY'): print(line.strip())
for k in sorted(tot): print(f'{k:20s} {tot[k]}')

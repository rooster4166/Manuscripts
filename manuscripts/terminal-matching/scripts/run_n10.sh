#!/bin/bash
# exhaustive n = 10: all iso classes of (G, F), |F| = M, PTM and PTM(r)
M=$1
cd "$(dirname "$0")"
./encode $M < out/odd10.g6 | nauty-labelg -q | sort -u -S 1G | python3 decode.py > out/n10/f$M.txt
split -n l/24 -d -a 2 out/n10/f$M.txt out/n10/f${M}_
ls out/n10/f${M}_?? | xargs -P 3 -I{} sh -c 'nice -n 10 ./ptm f '$M' 0 0 < {} > {}.out'
cat out/n10/f${M}_??.out | grep -v SUMMARY > out/n10_m${M}_fail.txt
python3 - $M <<'PY'
import sys, glob, collections
M = sys.argv[1]; tot = collections.Counter()
for f in sorted(glob.glob(f'out/n10/f{M}_??.out')):
    for line in open(f):
        if line.startswith('SUMMARY'):
            for kv in line.split()[1:]:
                k, v = kv.split('='); tot[k] += int(v)
print('TOTAL', dict(tot))
PY

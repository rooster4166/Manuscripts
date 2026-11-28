#!/bin/sh
# run_all.sh: regenerates every file in ../data (run from scripts/).  Budgets are those of the
# shipped files.  Needs g++, gcc, python3 with networkx.
set -e
MT=../../multi-token/data
RT=../../re-tight/scripts
g++ -O2 -o drm drm.cpp
gcc -O2 -o ret $RT/ret.c
gcc -O2 -DWIDE -o retw $RT/ret.c
# inputs
python3 mkB.py < $MT/J9_d6.g6 > ../data/B9.g6                       # B = J - z for ret.c
for f in resid_O8 resid_O10 e28_hard clt_hard; do python3 mkJ.py < $MT/$f.g6 > ../data/J_$f.g6; done
python3 frozen.py                                                   # frozen9.txt, Jfrozen_*.txt
# exact family check (Test1 at the roots of degree n - 2), order 9 and residual families
./ret -b 20000000 < ../data/B9.g6 > ../data/ret9.out
./ret -b 20000000 < $MT/resid_O8.g6 > ../data/ret_resid_O8.out
./retw -b 20000000 < $MT/resid_O10.g6 > ../data/ret_resid_O10.out
./retw -b 20000000 < $MT/e28_hard.g6 > ../data/ret_e28_hard.out
./ret -b 20000000 < $MT/clt_hard.g6 > ../data/ret_clt_hard.out
# the method at order 9
./drm < $MT/J9_d6.g6 > ../data/drm9.out                 # without -G: 1,750 YES, 6 NO
./drm -G < $MT/J9_d6.g6 > ../data/drm9G.out             # 1,756 YES
./drm -A -m 0 < $MT/J9_d6.g6 > ../data/drmA9_m0.out     # every-D, Phi separate: ALLD=1 at 1,742
./drm -A -m 1 < $MT/J9_d6.g6 > ../data/drmA9_m1.out
# frozen roots at order 9 (free paths allowed automatically for d_J(r) < n - 2)
./drm -G < ../data/frozen9.txt > ../data/frz9.out       # 112 YES, 1 NO (L = 3)
grep NO ../data/frz9.out | awk '{print $1, $2}' | ./drm -G -C 60 -L 6 > ../data/frz9_exception_L6.out
# residual families: randomised, budgeted (all UNK)
for seed in 1 2; do
  for f in resid_O8 resid_O10 e28_hard clt_hard; do
    ./drm -G -s $seed -C 8 -L 2 -b 100000 < ../data/J_$f.g6 > ../data/drm_${f}_s$seed.out
  done
  for f in resid_O8 resid_O10 e28_hard clt_hard; do
    ./drm -G -s $seed -C 8 -L 2 -b 100000 < ../data/Jfrozen_$f.txt > ../data/drmfrz_${f}_s$seed.out
  done
done
# heavier runs on three residual roots' graphs
head -2 ../data/J_resid_O8.g6 > ../data/heavy_in.g6; head -1 ../data/J_e28_hard.g6 >> ../data/heavy_in.g6
./drm -G -s 5 -C 3 -L 2 -b 20000000 < ../data/heavy_in.g6 > ../data/heavy.out
./drm -G -s 9 -C 3 -L 1 -m 0 -b 20000000 < ../data/heavy_in.g6 > ../data/heavy2.out
# coverage
python3 coverage.py order9 $MT/J9_d6.g6
for f in resid_O8 resid_O10 e28_hard clt_hard; do python3 coverage.py $f $MT/$f.g6 resid; done
python3 cov1597.py; python3 crosscheck.py $MT/J9_d6.g6; python3 look.py

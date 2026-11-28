#!/bin/sh
# method search on residual families (degree n-2 roots and frozen roots), randomized, budgeted
for seed in 1 2; do
  for f in resid_O8 resid_O10 e28_hard clt_hard; do
    ./drm -G -s $seed -C 8 -L 2 -b 100000 < J_$f.g6 > drm_${f}_s$seed.out
  done
  for f in resid_O8 resid_O10 e28_hard; do
    ./drm -G -s $seed -C 8 -L 2 -b 100000 < Jfrozen_$f.txt > drmfrz_${f}_s$seed.out
  done
done
echo done

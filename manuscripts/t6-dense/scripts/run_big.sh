#!/bin/sh
# E27 runs (session claude/t6-dense): residual-style graphs of every shape, and sparse C4 graphs.
# Summaries are copied into research/experiments.md (E27); raw logs stay in out/ (git-ignored).
set -e
cd "$(dirname "$0")"
gcc -O2 -o lsearch lsearch.c
for no in 8 10 12; do
  for sh in C4 K3 P3 K2 empty; do
    python3 gen_resid.py 20 $no 2 $((100 + no)) $sh > out/resid_${sh}_$no.g6 2>/dev/null || true
    python3 dense.py endZ 3 3000000 < out/resid_${sh}_$no.g6 > out/resid_${sh}_$no.log 2> out/resid_${sh}_$no.err
  done
done
python3 gen_resid.py 20 10 1 7 C4 > out/resid_C4tw1_10.g6 2>/dev/null
python3 dense.py endZ 3 3000000 < out/resid_C4tw1_10.g6 > out/resid_C4tw1_10.log 2> out/resid_C4tw1_10.err
for ne in 10 14; do
  python3 gen_core.py C4 30 $ne 5 > out/core_C4_$ne.g6 2>/dev/null
  python3 c4.py endA 3 3000000 < out/core_C4_$ne.g6 > out/core_C4_$ne.log 2> out/core_C4_$ne.err
done
grep -h SUMMARY out/*.log

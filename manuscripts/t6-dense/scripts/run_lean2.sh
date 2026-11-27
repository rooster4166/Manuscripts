#!/bin/sh
# E28 (session claude/t6-dense): remaining cells of run_lean.sh, two at a time, at most 60
# labellings per root (MAXLAB), exact Lean hypothesis (mode lean).
cd "$(dirname "$0")"
cell() {  # shape |O| twins seed
  python3 gen_resid.py 8 $2 $3 $4 $1 > out/lean_$1_$2.g6 2>/dev/null
  python3 dense.py lean 2 2000000 60 < out/lean_$1_$2.g6 > out/lean_$1_$2.log 2> out/lean_$1_$2.err
}
( cell empty 8 2 208; cell K3 10 2 210; cell K2 10 2 210 ) &
( cell C4 10 2 210; cell P3 10 2 210; cell empty 10 2 210 ) &
wait
python3 gen_resid.py 8 10 1 77 C4 > out/lean_C4tw1_10.g6 2>/dev/null
python3 dense.py lean 2 2000000 60 < out/lean_C4tw1_10.g6 > out/lean_C4tw1_10.log 2> out/lean_C4tw1_10.err
grep -h SUMMARY out/lean_*.log

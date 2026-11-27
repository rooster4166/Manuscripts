#!/bin/sh
# E28 main run (session claude/t6-dense): the exact Lean hypothesis AppendBase, on residual-style
# graphs of every shape (gen_resid.py) and on sparse graphs (gen_core.py).  Raw logs in out/.
set -e
cd "$(dirname "$0")"
gcc -O2 -o lsearch lsearch.c
for no in 8 10; do
  for sh in C4 K3 P3 K2 empty; do
    python3 gen_resid.py 8 $no 2 $((200 + no)) $sh > out/lean_${sh}_$no.g6 2>/dev/null || true
    python3 dense.py lean 2 2000000 < out/lean_${sh}_$no.g6 > out/lean_${sh}_$no.log 2> out/lean_${sh}_$no.err
  done
done
python3 gen_resid.py 8 10 1 77 C4 > out/lean_C4tw1_10.g6 2>/dev/null
python3 dense.py lean 2 2000000 < out/lean_C4tw1_10.g6 > out/lean_C4tw1_10.log 2> out/lean_C4tw1_10.err
for sh in C4 K3 empty; do
  python3 gen_core.py $sh 15 12 9 > out/lean_core_${sh}_12.g6 2>/dev/null
  python3 dense.py lean 2 2000000 < out/lean_core_${sh}_12.g6 > out/lean_core_${sh}_12.log 2> out/lean_core_${sh}_12.err
done
grep -h SUMMARY out/lean_*.log

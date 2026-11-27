#!/bin/sh
# Regenerate the quoted outputs of manuscripts/tight-fan (E26).  Requirements: gcc, python3 + networkx, nauty-geng.
set -e
gcc -O2 -o l1s ../../l1star/scripts/l1s.c
python3 xcheck.py > out/xcheck.txt                       # enumerator vs l1s oracle
python3 exp1c.py 7 2 > out/exp1c_7.txt                   # E26(A): inadmissible-but-good targets
python3 exp1c.py 7 0 max > out/exp1c_7max.txt
python3 exp1c.py 9 2 > out/exp1c_9.txt                   # (minutes)
python3 exp1c.py 9 0 max > out/exp1c_9max.txt
python3 exp1d.py 7 2 > out/exp1d_7.txt                   # E26(A): forced chain vs result
python3 exp1d.py 7 0 max > out/exp1d_7max.txt
python3 exp1e.py 7 2 > out/exp1e_7.txt                   # E26(A): tight sufficient condition
python3 exp1e.py 7 0 max > out/exp1e_7max.txt
python3 linf.py 7 > out/linf7.txt                        # E26(B)
python3 ptmwalk.py nowalk68.txt 7 > out/ptm_nowalk68.txt # E26(C)
python3 ee_inst.py > out/ee_inst.txt                     # E26(D)
# long runs (hours):
#   python3 linf.py 9 > out/linf9b.txt
#   python3 exp1e.py 9 2 > out/exp1e_9.txt
#   for k in 0 1 2; do python3 ptmwalk.py nobase764_s10.txt 6 $k 3 > out/ptm764s_$k.txt & done

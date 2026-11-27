#!/bin/sh
# Regenerate the outputs quoted in the manuscript that had no file (audit A21, N7).
set -x
gcc -O2 -march=native -o pee pee.c && cp pee peeall && cp pee pee3
gcc -O2 -o route_ext ../../../tools/route_ext.c
nauty-geng -cq 9 | ./peeall l1p all > out/l1p_9.txt
for n in 5 7; do nauty-geng -cq $n | ./peeall l1p all; done > out/l1p_5_7.txt
for n in 5 7; do nauty-geng -cq $n | ./peeall sepee | grep -v SEPFAIL; done > out/sepee_5_7.txt
for n in 5 7; do nauty-geng -cq $n | python3 tri_sep.py; done > out/tri_sep_5_7.txt
for n in 5 6 7 8; do nauty-geng -cq $n | ./peeall l1s2; done > out/l1s2_5_8.txt
for n in 7 9; do nauty-geng -cq $n | ./peeall g6 w | python3 sharp.py; done > out/sharp_7_9.txt
python3 feat.py out/exh9.txt > out/feat_9.txt
python3 analyze_fail.py out/exh9.txt > out/analyze_fail_9.txt
for n in 4 5 6 7; do nauty-geng -cq $n | python3 brute.py; done > out/brute_4_7.txt
for n in 4 6 8; do nauty-geng -cq $n | ./peeall g6; done > out/allodd_4_8.txt
nauty-geng -cq 9 | python3 xcheck_route_ext.py ./route_ext > out/xcheck_route_ext_9.txt

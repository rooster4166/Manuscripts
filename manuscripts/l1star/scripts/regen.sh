#!/bin/sh
# Regenerates every output quoted in l1star.tex except the long runs
# (exhaustive order 11: run_n11.sh; random: rand_max.py; order-7 brute-force cross-check).
set -e
cd "$(dirname "$0")"
gcc -O2 -march=native -o l1s l1s.c
for n in 5 6 7 8 9 10; do nauty-geng -cq $n | ./l1s max 4 q > out/max$n.txt; done
for n in 5 6 7; do nauty-geng -cq $n | ./l1s max 3 n > out/maxn$n.txt; done
nauty-geng -cq 9 | ./l1s gen 4 > out/gen9.txt
for n in 5 6 7 8; do nauty-geng -cq $n | ./l1s stats > out/stats$n.txt; done
for n in 6 8 10; do nauty-geng -cq $n | ./l1s two > out/two$n.txt; done
for n in 6 7 8 9 10; do nauty-geng -cq $n | ./l1s packedev > out/packedev$n.txt; done
for n in 6 8 9 10; do nauty-geng -cq $n | ./l1s peloc > out/peloc$n.txt; done
for n in 7 9; do nauty-geng -cq $n | python3 blocked_count.py 2 > out/blocked_count$n.txt; done
for n in 7 9; do nauty-geng -cq $n | python3 irred_all.py 2 > out/irred_all$n.txt; done
for n in 6 8; do nauty-geng -cq $n | python3 te3walk.py 4 > out/te3walk$n.txt; done
for n in 4 5 6; do nauty-geng -cq $n | python3 xcheck_brute.py | tail -1; done > out/xcheck_4_6.txt

#!/bin/sh
# run.sh: regenerate ../data (except the long order-9 classification, see classify9.sh).
# Needs nauty-geng only for the optional order-11 slice at the end; the one-even lists are those of
# ../../stl/scripts.
set -e
O=../../stl/scripts; D=../data
./build.sh
# validation: C++ enumerator + forced chain against the independent Python brute force
for k in 5 7; do ./chainlist < $O/one_even_$k.g6 | sort > /tmp/trn_cl$k.txt; python3 brute.py < $O/one_even_$k.g6 | sort > /tmp/trn_br$k.txt; done
( for k in 5 7; do printf "order %s: %s instances, " $k $(wc -l < /tmp/trn_cl$k.txt); if cmp -s /tmp/trn_cl$k.txt /tmp/trn_br$k.txt; then echo "identical (nD, nAvoid, nGood) for every instance"; else echo "MISMATCH"; fi; done ) > $D/validation.txt
# TRN and TRN-E, exhaustive at orders 5, 7, 9
( for k in 5 7 9; do echo "order $k"; ./trne 0 < $O/one_even_$k.g6 | tail -1; done ) > $D/trne.txt
# random graphs, orders 11 and 13 (400 graphs, seed 11)
python3 randg.py 400 11 11 13 > /tmp/trn_r1113.g6
./trnbud 2000000 < /tmp/trn_r1113.g6 > $D/random_11_13.txt
# the core of Definition 5.1
( for k in 5 7 9; do echo "order $k"; ./core < $O/one_even_$k.g6; done ) > $D/core.txt
# instance-level classes and extremal rules (orders 5, 7)
( for k in 5 7; do echo "order $k"; ./chain 0 0 < $O/one_even_$k.g6 | sed '/capped/d'; ./minchain < $O/one_even_$k.g6; ./rules < $O/one_even_$k.g6; done ) > $D/instances57.txt
# (G, D') classification, exhaustive at orders 5 and 7, all tests and the core
( ./classify 0 < $O/one_even_5.g6; ) > $D/classify5.txt
./classify 6 < $O/one_even_7.g6 > $D/classify7.txt
CORE=1 ./classify 10 < $O/one_even_7.g6 > $D/classify7_core.txt
# repairs restricted to tests whose child has a witness (order 7)
( WIT=1 ./rot 0 < $O/one_even_7.g6 | tail -1; WIT=1 ./halves < $O/one_even_7.g6 | tail -1; WIT=1 ./local 0 0 < $O/one_even_7.g6 | tail -1 ) > $D/repairs7_witness.txt
# two-token steering (Section 6): coverage on N-instances, all-tight ones, the residual, the core
g++ -O2 -I ../../l1-induction/scripts -o steer steer.cpp
g++ -O2 -I ../../l1-induction/scripts -o steer2 steer2.cpp
( for k in 5 7 9; do echo "order $k"
    ./steer N 0 0 < $O/one_even_$k.g6 | tail -1                 # move (T): the y-token only (independent DFS)
    ./steer2 N 2000000 1 0 < $O/one_even_$k.g6 | tail -1        # the same with steer2 (cross-check)
    ./steer2 N 2000000 0 0 < $O/one_even_$k.g6 | tail -1        # two tokens
    ./steer2 RESID 2000000 0 0 < $O/one_even_$k.g6 | tail -1
    ./steer2 CORETESTS 2000000 0 0 < $O/one_even_$k.g6 | tail -1
  done ) > $D/steer.txt
# independent verification of the construction (every schedule at orders 5, 7)
( for k in 5 7; do SCHED=1 ./steer2 N 2000000 0 0 < $O/one_even_$k.g6 | python3 steer_verify.py; done ) > $D/steer_verify57.txt

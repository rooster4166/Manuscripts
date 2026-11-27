#!/bin/sh
# regen.sh: regenerate every output quoted in l1-induction.tex, E27 and §AC (after audit A25, F18).
# Long runs (order 9 TR, Rec with every route, order-11 slices, random runs) are listed at the end.
set -e
for t in rec rec2 tt tr2 trall rechoice exch stprime l1e targets alltarget gap minobs walk2 walkadm xcheck2 randtest example qedge; do
  g++ -O2 -std=c++17 -o $t $t.cpp
done
G=nauty-geng
mkdir -p out
# validation
for n in 4 5 6 7; do $G -cq $n | ./xcheck2; done > out/xcheck2_4_7.txt
# Rec: (a)-(d) only, and with all moves; every admissible A at orders 4-8; |A| <= 2 at order 7
for n in 6 7 8; do $G -cq $n | ./rec adm | tail -1; done > out/rec_ad_only_6_8.txt
for n in 4 5 6 7 8; do $G -cq $n | ./rec2 subsets MB | tail -1; done > out/rec_subsets_4_8.txt
$G -cq 7 | KS=2 ./rec2 subsets MB | tail -1 > out/rec_small7.txt
$G -cq 7 | ./rec2 subsets MBT | tail -1 >> out/rec_small7.txt
# TR, sharpness, re-choice, coverage, ST/ST', L1E at small orders
$G -cq 7 | ./tr2 > out/tr2_7.txt
for n in 5 7; do $G -cq $n | ./trall; done > out/trall_5_7.txt
for n in 5 7; do $G -cq $n | ./rechoice | tail -1; done > out/rechoice_5_7.txt
$G -cq 7 | ./exch > out/exch7.txt
$G -cq 7 | ./stprime > out/stprime7.txt
for n in 5 7 9; do $G -cq $n | ./l1e | tail -1; done > out/l1e_5_9.txt
# targets and the every-target form
$G -cq 9 | ./targets > out/targets9_summary.txt
$G -cq 9 | ./alltarget > out/alltarget9.txt
# gaps, dead ends, walks
for n in 6 7 8; do $G -cq $n | ./gap 6 | tail -1; done > out/gap_6_8.txt
for n in 7 8; do $G -cq $n | TR=1 ./gap 6 | tail -1; done > out/gap_6_8_TR.txt
for n in 5 7; do $G -cq $n | ./minobs 6 4; done > out/minobs_5_7.txt
for m in 0 1 2 3; do for n in 7 9; do $G -cq $n | ./walk2 $m 40 | tail -1; done; done > out/walk2_7_9.txt
for n in 7 9; do $G -cq $n | ./walkadm 40 | tail -1; done > out/walkadm_7_9.txt
./example "FEhv?" 6 3,5 > out/example_FEhv.txt
./example "FCZ~o" 0 1,2,3,4 > out/example_FCZo.txt
grep STUCK0 out/stuck0_9.txt | awk '{print $2, $3, $4}' | ./qedge > out/qedge_stuck9.txt
echo "short runs done"
# Long runs (hours in total):
#   nauty-geng -cq 9 | ./tr2 > out/tr2_9.txt
#   nauty-geng -cq 9 | ./rec2 adm MBR  > out/rec_adm9_MBR.txt     # (h) along every route
#   nauty-geng -cq 9 | ./rec2 adm MBTR > out/rec_adm9_MBTR.txt
#   for k in 0 1 2 3; do nauty-geng -cq 11 $k/100 | ./randtest 2000000 > out/slice11_${k}of100.txt; done
#   python3 randg.py 3000 27 11 13 | ./randtest 2000000 > out/rand_11_13_v3.txt
#   python3 randg.py 600 41 15     | ./randtest 2000000 > out/rand_15_v3.txt

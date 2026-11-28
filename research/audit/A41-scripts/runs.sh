#!/bin/sh
# A41 (nodata): every command the auditor ran.  S = scratch directory, A = research/audit/A41-scripts.
A=research/audit/A41-scripts; S=${S:-/tmp/a41}; mkdir -p $S
# Lean
(cd lean && lake build && lake env lean ../$A/axioms.lean && lake env lean GallaiLean/NoData.lean)
# build
g++ -O2 -std=gnu++17 -o $S/a41 $A/a41.cpp
g++ -O2 -std=gnu++17 -o $S/a41rm $A/a41rm.cpp
g++ -O2 -std=gnu++17 -o $S/a41nd $A/a41nd.cpp
g++ -O2 -o $S/a41odd $A/a41odd.cpp
# examples (brute force over all Lovasz decompositions) and the explicit fat-theta decomposition
python3 -I $A/examples_bruteforce.py
python3 -I $A/fat_theta_explicit.py
# (T1) tiers, n <= 9 (orders 5, 7, 9), and per-root comparison with data/nd_t1_le9.txt
(nauty-geng -q -C -d3 5; nauty-geng -q -C -d3 7; nauty-geng -q -C -d3 9) > $S/gle9.g6
$S/a41 tiers < $S/gle9.g6 > $S/mine_le9.txt
# universality (every structure) at n <= 9, and the (H1) split of the tier-3 structures
$S/a41 univ < $S/gle9.g6 > $S/univ_le9.txt 2> $S/univ_le9.err
python3 -I $A/univ_h1.py < $S/univ_le9.txt
# order 11: the tier-4/5 roots of data/nd_t1_11_ge2.txt.gz, re-classified from scratch
zcat manuscripts/nodata/data/nd_t1_11_ge2.txt.gz | awk '$1=="ND" && ($16==4||$16==5){print $2}' | uniq > $S/t45_11.g6
$S/a41 tiers < $S/t45_11.g6 > $S/t45_11_mine.txt
# root moves: n <= 9, order 11 tier >= 2, and the full order-11 census + closure
$S/a41rm 6 < manuscripts/nodata/data/nd_t1_le9.txt > $S/rm_le9.txt
zcat manuscripts/nodata/data/nd_t1_11_ge2.txt.gz | $S/a41rm 6 > $S/rm_11ge2.txt
nauty-geng -q -C 10 | $S/a41nd 2> $S/census11.err | $S/a41rm 6 2> $S/rm11all.err > /dev/null
# order 11: systematic 1/300 sample, tiers 1-2 decided from scratch (tier >= 3 not searched)
nauty-geng -q -C 10 | awk 'NR % 300 == 17' | $S/a41nd 2>/dev/null | awk '{print $2}' | uniq > $S/sample11.g6
A41_MAXTIER=2 $S/a41 tiers < $S/sample11.g6 > $S/sample11_tiers.txt
# abstract families, orders 4, 6, 8
for n in 4 6 8; do nauty-geng -q -c $n; done > $S/c468.g6
for f in k r c l lp lk kp kk kpp cp ss; do $S/a41 fam $f < $S/c468.g6 > $S/fam_$f.txt 2> $S/fam_$f.err; done
for f in s sp sk; do A41_SKIP_H1=1 $S/a41 fam $f < $S/c468.g6 > $S/famH_$f.txt 2> $S/famH_$f.err; done
# order 10: the number of one-2-chain sets
nauty-geng -q -c 10 | $S/a41odd > $S/odd10.g6    # 32,851 graphs

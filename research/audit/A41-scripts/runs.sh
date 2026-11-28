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
# --- added later in the audit ---
# universality with the (sound) extra pruning, and the exact populations without solving
A41_PRUNE=1 $S/a41 univ < $S/gle9.g6 > $S/univP_le9.txt 2> $S/univP_le9.err
A41_COUNTONLY=1 $S/a41 univ < $S/gle9.g6 > /dev/null
python3 -I $A/univ_h1.py $S/mine_le9.txt < $S/univP_le9.txt
# the truncation of nd.c -U at tier 3: run the authors' nd.c (compiled in the scratch dir) and compare
gcc -O2 -o $S/nd_auth manuscripts/nodata/scripts/nd.c
$S/nd_auth -t1 -UU < $S/gle9.g6 2>&1 >/dev/null | tail -2          # tier3 32706/88148
$S/nd_auth -t1 -UU < $S/gle9.g6 2>/dev/null | awk '$5=="tier" && $6=="3"' | awk '{tag=($1=="UFAIL")?"FAIL":"SUCC"; printf "U3 %s %s %s %s", tag, $2, $3, $4; for(i=7;i<=NF;i++) printf " %s", $i; printf "\n"}' > $S/nduu3.txt
python3 -I $A/univ_h1.py $S/mine_le9.txt < $S/nduu3.txt               # reproduces star_hall_t1_le9.txt
# the star + 2-chain + pair failures with (H1) holding, by brute force; and the explicit example
grep -E '^U3 FAIL (H\?bc~f\{|H\?qu\\v\{) ' $S/univP_le9.txt > $S/scp_in.txt
python3 -I $A/star_chain_pair.py $S/scp_in.txt
python3 -I $A/star_chain_pair_example.py
# order-11 sample comparison; order-10 set counts
python3 -I $A/cmp_sample11.py $S/sample11_tiers.txt manuscripts/nodata/data/nd_t1_11_ge2.txt.gz
python3 -I $A/count10.py < $S/odd10.g6

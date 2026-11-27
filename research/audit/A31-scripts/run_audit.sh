#!/bin/bash
# run_audit.sh (auditor, conj-n audit): the runs of research/audit/A31-conj-n.md.
# usage: run_audit.sh SCRATCH_DIR      (builds the authors' tools unmodified into SCRATCH_DIR/bin)
set -e
S=${1:?scratch dir}; mkdir -p "$S/bin" "$S/out"
SC=/home/user/Manuscripts/manuscripts/conj-n/scripts
L=/home/user/Manuscripts/manuscripts/l1-induction/scripts
O=/home/user/Manuscripts/manuscripts/stl/scripts
A=/home/user/Manuscripts/research/audit/A31-scripts
cd "$SC"
for t in ncert closure2 xcert tx nplus gplus nadj tradj trn qb; do g++ -O2 -I "$L" -o "$S/bin/$t" $t.cpp; done
gcc -O2 -o "$S/bin/allodd" allodd.c
g++ -O2 -I "$SC" -I "$L" -o "$S/bin/movecheck" "$A/movecheck.cpp"
cd "$S"
# certificates
for k in 5 7 9; do ./bin/ncert < $O/one_even_$k.g6 > out/ncert$k.txt; tail -n1 out/ncert$k.txt; done
grep UNCERT out/ncert9.txt | awk '{print $2}' | sort -u > out/unc9.g6
./bin/xcert < out/unc9.g6 | tail -n1
for e in xC xCk x C k; do echo "xcert excluding [$e]: $(./bin/xcert $e < out/unc9.g6 | tail -n1)"; done
# conjecture tests
for k in 5 7 9; do ./bin/trn < $O/one_even_$k.g6 | tail -n1; ./bin/nplus < $O/one_even_$k.g6 | tail -n1; ./bin/tx < $O/one_even_$k.g6 | tail -n1; done
./bin/gplus < $O/one_even_9.g6 | tail -n1
./bin/tradj < $O/one_even_7.g6 | tail -n1; ./bin/tradj 2 < $O/one_even_9.g6 | tail -n1
for n in 4 6 8 10; do nauty-geng -cq $n | ./bin/allodd | ./bin/nadj | tail -n1; done
for s in 17 517; do nauty-geng -cq 11 $s/2000 | ./bin/trn | tail -n1; done
# closure
./bin/closure2 N1NA -T2 -b 0 -p 0 < $O/one_even_9.g6 | tail -n1
./bin/closure2 N1 -b 0 -p 1000000 < $O/one_even_9.g6 > out/cl_N1_9.txt
python3 -I $SC/n1stuck.py < out/cl_N1_9.txt | tail -n1
python3 -I $A/alltight.py $O/one_even_9.g6 out/cl_N1_9.txt
nauty-geng -cq 7 | ./bin/closure2 C1 -T2 -b 0 -g -p 100000 | python3 -I $A/stuckfeat.py STUCK
nauty-geng -cq 7 | ./bin/closure2 N2 -T2 -b 0 -g -p 100000 | python3 -I $A/stuckfeat.py STUCK
nauty-geng -cq -D3 7 | ./bin/closure2 D_N2 -D 3 -G 2 -b 0 -g -p 100000 | python3 -I $A/stuckfeat.py STUCK
nauty-geng -cq 6 | ./bin/closure2 N1NA -T2 -b 0 -g -p 1000 | python3 -I $A/stuckfeat.py STUCK
nauty-geng -cq 5 | ./bin/closure2 N2B -s -p 1000 | python3 -I $A/stuckfeat.py FALSE
bash $A/tables_aud.sh   # writes $S/out/tables.txt (paths edited for this scratch dir); compare with data/tables.txt
# move soundness (all moves of ext.h against the exact oracle)
for n in 3 4 5 6 7 8; do nauty-geng -cq $n | ./bin/movecheck | head -n1; done
nauty-geng -q 7 | ./bin/movecheck | head -n1
nauty-geng -cq 7 | ./bin/movecheck -T2 | grep "move t"
nauty-geng -cq 7 | ./bin/movecheck -L 8 | grep "move k"
shuf -n 600 --random-source=<(yes) $O/one_even_9.g6 > out/sample9.g6
./bin/movecheck -a 2 -b 1 < out/sample9.g6 | head -n1
head -n 120 out/sample9.g6 | ./bin/movecheck -a 3 -b 3 | head -n1
# variants (power check; uncapped leaf paths and routes)
bash $A/make_variants.sh "$S/mv"

#!/bin/bash
# rerun.sh: regenerate every file of ../data from scratch (hours; order 10 NA and order 11 TRN dominate).
set -e
I=../../l1-induction/scripts; O=../../stl/scripts
for t in ncert closure2 xcert tx nplus gplus nadj tradj trn qb nadjstat; do g++ -O2 -I $I -o $t $t.cpp; done
gcc -O2 -o allodd allodd.c; (cd ../../dl-one/scripts && gcc -O2 -o enum enum.c)
mkdir -p out
./ncert BMSR < $O/one_even_9.g6 > out/ncert9.txt
grep UNCERT out/ncert9.txt > ../data/ncert9_uncertified.txt
awk '{print $2}' ../data/ncert9_uncertified.txt | sort -u > out/unc9.g6
./xcert < out/unc9.g6 | grep -E "UNCERT|XCERT" > ../data/xcert9_uncertified.txt
./tables.sh; cp out/tables.txt ../data/tables.txt
./closure2 N1 -b 0 -p 1000000 < $O/one_even_9.g6 | python3 n1stuck.py $O/one_even_9.g6 > ../data/n1_stuck9.txt
for n in 5 7; do nauty-geng -cq $n | ./closure2 N1 -b 0 -p 1000000 | python3 n1stuck.py <(nauty-geng -cq $n) | tail -1; done > ../data/n1_stuck57.txt
{
echo "# Conjecture tests (exhaustive over the stated graphs; exact oracle)"
echo "## N (ncert.cpp, calculus of l1-induction Thm 3.1 + bases; R = every route for (h))"; for k in 5 7 9; do echo "n=$k $(./ncert BMSR < $O/one_even_$k.g6 | tail -1)"; done
echo "## N+ : (G,y,{x},N(x)) for N instances (nplus.cpp)"; for k in 5 7 9; do echo "n=$k $(./nplus < $O/one_even_$k.g6 | tail -1)"; done
echo "## (x)-child of x~g instances, core = N(g)-{x,y} inside N(x) (tx.cpp)"; for k in 5 7 9; do echo "n=$k $(./tx < $O/one_even_$k.g6 | tail -1)"; done
echo "## Q_c avoids g, far version (gplus.cpp)"; for k in 5 7 9; do echo "n=$k $(./gplus < $O/one_even_$k.g6 | tail -1)"; done
echo "## TRN (trn.cpp), one forbidden vertex, both y~g and y!~g"; for k in 5 7 9; do echo "n=$k $(./trn < $O/one_even_$k.g6 | tail -1)"; done
echo "order 11 slices 17/2000 and 517/2000: $(nauty-geng -cq 11 17/2000 | ./trn | tail -1) | $(nauty-geng -cq 11 517/2000 | ./trn | tail -1)"
echo "## TR* with c~g (tradj.cpp): n=5,7 all A; n=9 |A|<=2"; for k in 5 7; do echo "n=$k $(./tradj < $O/one_even_$k.g6 | tail -1)"; done; echo "n=9 $(./tradj 2 < $O/one_even_9.g6 | tail -1)"
nauty-geng -cq 10 | ./allodd > out/allodd10.g6
echo "## NA (nadj.cpp), all-odd connected graphs"; for n in 4 6 8; do echo "n=$n $(nauty-geng -cq $n | ./allodd | ./nadj | tail -1)"; done; echo "n=10 ($(wc -l < out/allodd10.g6) graphs) $(./nadj < out/allodd10.g6 | tail -1)"
echo "## NA cases (nadjstat.cpp): d(y)=3 (split (g)), d(x)=1 (Lemma NP), no common neighbour (dl-one Thm 6.1), rest"; for n in 6 8; do echo "n=$n $(nauty-geng -cq $n | ./nadjstat)"; done; echo "n=10 $(./nadjstat < out/allodd10.g6)"
echo "## far-end oracle vs enumeration (xcheckb.py)"; echo "$( (for n in 4 5 6; do nauty-geng -cq $n; done; cat $O/one_even_7.g6) | python3 xcheckb.py | tail -1)"
} > ../data/conjecture_tests.txt 2>&1

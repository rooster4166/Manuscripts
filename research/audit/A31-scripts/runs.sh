#!/bin/sh
# A31 audit of manuscripts/re-tight at commit 61dbe23: every command the auditor ran.
# Scratch: /tmp/claude-0/a31 (not committed).  Run from the repository root.
set -e
A=$(pwd)/research/audit/A31-scripts
T=/tmp/claude-0/a31
E=$(pwd)/manuscripts/eulerian-cone/data
mkdir -p $T/snap $T/data
# audit the committed snapshot, not the working tree (another session was editing ret.c)
git archive 61dbe23 manuscripts/re-tight lean/GallaiLean/RETight.lean | tar -x -C $T/snap
O=$T/snap/manuscripts/re-tight/data/out; S=$T/snap/manuscripts/re-tight/scripts
for f in retL_10 retT_10 ret_10 retz_10_partial; do zcat $O/$f.txt.gz > $T/data/$f.txt; done

# Lean: axioms, signatures, non-vacuity; full build
(cd lean && export PATH=$HOME/.elan/bin:$PATH && lake env lean $A/axioms.lean && lake build)

# shipped checkers on shipped data
for f in $O/ret_4.txt $O/ret_6.txt $O/ret_8.txt $T/data/ret_10.txt $O/retL_6.txt $O/retL_8.txt \
         $T/data/retL_10.txt $O/retL_mid12.txt $O/retL_nr.txt $O/retL_mixed16.txt $O/ret_mixed16.txt; do
  python3 -I $S/verify_family.py < $f | tail -1; done
for f in $O/retz_6.txt $O/retz_8.txt $T/data/retz_10_partial.txt; do python3 -I $S/verify_family.py -z < $f | tail -1; done
python3 -I $S/compare_z.py $O/p_6.txt $O/retz_6.txt
python3 -I $S/compare_z.py $O/p_8.txt $O/retz_8.txt
python3 -I $S/compare_z.py $O/p_10.txt $T/data/retz_10_partial.txt
for n in 6 8; do python3 -I $S/coverage.py $n $O/retL_$n.txt; done
python3 -I $S/coverage.py 10 $T/data/retL_10.txt $T/cov10_mine.txt; cmp $T/cov10_mine.txt $O/cov_10.txt
python3 -I $S/check_star.py $O/retT_8.txt; python3 -I $S/check_star.py $T/data/retT_10.txt

# own recount of Table 1, the 77/19/58 split, the 147 roots, -T, tight roots
python3 -I $A/recount.py $E $O $T/data
# own Lovasz-family check of every -L witness
python3 -I $A/verify_lovasz.py $O/retL_6.txt $O/retL_8.txt $T/data/retL_10.txt $O/retL_mid12.txt $O/retL_nr.txt $O/retL_mixed16.txt
# own re-decision of the -z answers at orders 6, 8
python3 -I $A/zcheck.py $O/retz_6.txt $O/retz_8.txt
# Example 4.2 and Prop 4.1 arithmetic; Remark 3.4 family
python3 -I $A/example42.py
python3 -I $A/whatsnew.py $T/whatsnew.txt
# order 12/16 samples
python3 -I $A/samples_check.py $E $O

# independent Lovasz enumeration (lovcheck.c) against ret -T / -L
gcc -O2 -march=native -o $T/lovcheck $A/lovcheck.c
gcc -O2 -o $T/evenn2 $A/evenn2.c
$T/lovcheck < $O/hasn2_6.g6 > $T/lc6.txt; python3 -I $A/cmp_lov.py $T/lc6.txt $O/retT_6.txt $O/retL_6.txt
$T/lovcheck < $O/hasn2_8.g6 > $T/lc8.txt; python3 -I $A/cmp_lov.py $T/lc8.txt $O/retT_8.txt $O/retL_8.txt
# order 10: the 15 -T failures and 600 random -T DONE roots with <= 300,000 decompositions (seed 31)
python3 -I -c "
import random; random.seed(31)
L=[l.split() for l in open('$T/data/retT_10.txt')]
done=[f for f in L if f[2]=='DONE']
fail=[f for f in done if int(f[4].split('=')[1])<int(f[5].split('=')[1])]
small=[f for f in done if int(f[3].split('=')[1])<=300000 and f not in fail]
o=open('$T/t10_sample.txt','w')
for f in fail+random.sample(small,600): o.write('%s %s\n'%(f[0],f[1]))"
$T/lovcheck -noL < $T/t10_sample.txt > $T/lc10T.txt
python3 -I $A/cmp_lov.py $T/lc10T.txt $T/data/retT_10.txt
# Theorem 3.1 on ALL even graphs with a degree-(n-2) vertex, any connectivity (orders 4-8), and on
# all not-2-connected ones of order 10 (cap 10^6 decompositions per root)
for n in 4 6 8; do nauty-geng -q $n | $T/evenn2 > $T/even_$n.g6
  $T/lovcheck -noL < $T/even_$n.g6 > $T/lce_$n.txt; python3 -I $A/cmp_lov.py $T/lce_$n.txt; done
nauty-geng -q 10 | $T/evenn2 -n2c > $T/evenn2c_10.g6
$T/lovcheck -noL -c 1000000 < $T/evenn2c_10.g6 > $T/lce_10n2c.txt; python3 -I $A/cmp_lov.py $T/lce_10n2c.txt
# Step 5 executed literally (all theorem orientations, <= 2000 decompositions per root)
for n in 4 6 8; do python3 -I $A/step5.py $T/even_$n.g6 2000; done
# Hamiltonian paths in the Lovasz decompositions at the order-8 failures
python3 -I $A/ham_frac.py 'G]zn^[' 2 'G]~vvs' 4 'G]~v~w' 0 'G??F~w' 6
# the committed ret.c against the shipped outputs (order 8, nr12, a 150-graph order-10 sample)
gcc -O2 -march=native -o $T/ret_snap $S/ret.c
$T/ret_snap < $E/euler2c_8.g6 | cmp - $O/ret_8.txt
$T/ret_snap -z < $O/hasn2_8.g6 | cmp - $O/retz_8.txt
$T/ret_snap -L -b 200000000 < $O/hasn2_8.g6 > $T/rL8.txt; cmp $T/rL8.txt $O/retL_8.txt || true
$T/ret_snap -T -b 50000000 < $O/hasn2_8.g6 > $T/rT8.txt; cmp $T/rT8.txt $O/retT_8.txt || true
python3 -I -c "
import random; random.seed(311)
L=open('$O/hasn2_10.g6').readlines(); open('$T/h10_s150.g6','w').writelines(random.sample(L,150))"
$T/ret_snap -L -b 20000000 < $T/h10_s150.g6 > $T/rL10s.txt
python3 -I $A/verify_lovasz.py $T/rL10s.txt
# Remark 3.4 family under lovcheck (first 3e5 / 1e5 decompositions per root)
head -2 $T/whatsnew.txt | $T/lovcheck -noL -c 300000
tail -2 $T/whatsnew.txt | timeout 900 $T/lovcheck -noL -c 100000
# one of the 58 undecided order-10 roots: count, then exhaustive -L
echo "ITm~vvz}w 0" | $T/lovcheck -noL   # stderr: decompositions with a Hamiltonian path
echo "ITm~vvz}w 0" | $T/lovcheck -l
# commit 376ea05 (landed during the audit): order-12 random numbers
mkdir -p $T/snap2; git archive 376ea05 manuscripts/re-tight | tar -x -C $T/snap2
zcat $T/snap2/manuscripts/re-tight/data/out/retL_rand12_all.txt.gz > $T/data/retL_rand12_all.txt
python3 -I $A/verify_lovasz.py $T/data/retL_rand12_all.txt
python3 -I -c "
import sys; sys.path.insert(0,'$A')
from g6 import parse_g6
from recount_conditions import star2
from collections import Counter
c=Counter()
for l in open('$T/data/retL_rand12_all.txt'):
    f=l.split(); n,adj=parse_g6(f[0]); u=sum(1 for a in adj if len(a)==n-2)
    c[('in170' if u>=n//2-1 else 'out170', f[2], star2(n,adj,int(f[1])))]+=1
print(c)"

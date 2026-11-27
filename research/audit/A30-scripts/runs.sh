#!/bin/sh
# A30 audit: the commands the auditor ran (scratch outputs in /tmp/claude-0, not committed).
# M = manuscripts/eulerian-cone ; run from the repository root.
set -e
M=manuscripts/eulerian-cone; S=$M/scripts; D=$M/data; O=$M/data/out; A=research/audit/A30-scripts; T=/tmp/claude-0
mkdir -p $T
gcc -O2 -o $T/audit_re $S/re.c
gcc -O2 -o $T/a30_oddfilter $S/oddfilter.c
gcc -O2 -o $T/a30_evenfilter $S/evenfilter.c

# 1. brute force vs re.c (manuscript's validation, re-run): 473 graphs, 3,622 values, 0 mismatches
for n in 3 4 5 6 7; do nauty-geng -cq $n 0:10; done > $T/a30_small.g6
python3 $S/bf.py < $T/a30_small.g6 > $T/a30_small.bf
$T/audit_re -x < $T/a30_small.g6 > $T/a30_small.re; $T/audit_re -p < $T/a30_small.g6 > $T/a30_small.rep
python3 $S/verify_witness.py < $T/a30_small.re; python3 $S/compare_bf.py $T/a30_small.bf $T/a30_small.re $T/a30_small.rep
# 1b. bf.py on the 102 connected Eulerian graphs of order <= 8 with <= 13 edges, compared with
#     the shipped tables (753 roots, 0 mismatches; comparison done inline in the session)

# 2. tables: own CB implementation, RE*, UC by 2-connectivity (Section 6, 7)
python3 $A/recount.py $O
(cd $S && python3 summary.py)

# 3. the 8 uncertified order-10 roots: witnesses (all verified)
for x in "IEl}}~^vw 0" "IEl}}~^vw 1" "IEl}}~^vw 2" "ITzvn^nzw 4" "ITm||~}~g 1" "ITm||~}~g 7" "I]zn^^nzw 0" "I]zn^^nzw 1"; do
  set -- $x; echo "$1" | $T/audit_re -d -r $2; done | python3 $S/verify_witness.py
echo 'ITzvn^nzw' | $T/audit_re -r 4 | python3 $S/verify_witness.py        # p_r = 4

# 4. examples, matching cuts, Section 5 structure, UC failures by CP-SAT
python3 $A/examples.py
python3 $A/mcut_check.py $D/euler2c_4.g6 $D/euler2c_6.g6 $D/euler2c_8.g6 $D/euler2c_10.g6
python3 $A/structure_check.py $D/euler_conn_[4-9].g6 $D/euler_conn_10.g6
(cd $S && python3 cpsat_check.py ../../../$A/ucfail_roots.txt)
(cd $S && python3 reductions_check.py $T/audit_re ../data/euler_conn_[4-8].g6)

# 5. dense order 12: regenerate (124,004), UC with witnesses at all 1,488,048 roots
nauty-geng -d1 -q 12 0:20 | $T/a30_oddfilter | nauty-complg -q > $T/a30_dense12.g6
python3 -c "
import networkx as nx
o=open('$T/a30_dense12_2c.g6','w')
for x in open('$T/a30_dense12.g6'):
    if nx.is_biconnected(nx.from_graph6_bytes(x.strip().encode())): o.write(x)"
$T/audit_re -u -b 2000000 < $T/a30_dense12_2c.g6 | python3 $A/verify_uc.py
# 5b. the missing slice m = 45 (complement with exactly 21 edges): 134,770 graphs
nauty-geng -d1 -q 12 21:21 | $T/a30_oddfilter | nauty-complg -q > $T/a30_m45.g6
#     (filter to 2-connected as above: 134,770 graphs, file $T/a30_m45_2c.g6, then)
#     $T/audit_re -u -b 2000000 < $T/a30_m45_2c.g6 | python3 $A/verify_uc.py   -> 1,617,237 UC + 3 OKUNK
#     the 3 OKUNK roots ($A/m45_unk.txt): unbudgeted re.c and CP-SAT both find 5 paths
#     (cd $S && python3 cpsat_decide.py ../../../$A/m45_unk.txt 900 | python3 verify_witness.py)

# 6. order 14, 4-regular (table not shipped): RE with witnesses at all 1,233,764 roots
zcat $D/reg14_4.g6.gz | $T/audit_re -d -b 50000000 | python3 $S/verify_witness.py

# 7. Lean axioms
(export PATH=$HOME/.elan/bin:$PATH; cd lean && lake env lean ../$A/axioms.lean)

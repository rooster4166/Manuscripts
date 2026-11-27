#!/bin/bash
# Audit A12: reproduce every output in out/ (independent solver; about an hour on one core; the criticality check of the 47 is the slow part).
set -e
cd "$(dirname "$0")"
O=../../../manuscripts/missing-move/scripts/outputs
D=../../../data
P="nice -n 15 python3"
mkdir -p out
# certificates printed by the author
( $P cert_replay.py 'Gqz~vw' 3 $O/certificate_Gqz.txt
  $P cert_replay.py 'Gr~v~w' 0 $O/certificate_K8M.txt
  $P cert_replay.py 'I~~~wF{~G' 0 $O/certificate_B2.txt
  $P cert_replay.py 'Inv~|~zbw' 2 $O/certificate_miss1.txt
  $P cert_replay.py 'Inv~|~zbw' 3 $O/certificate_miss1.txt
  for gr in "GsRvnk 2" "GsRvnk 3" "GsZvnk 4" "Gqrvn[ 2" "Gqzvn[ 4" "Gqzl|{ 1"; do
    set -- $gr; $P cert_replay.py "$1" $2 $O/certificates.txt "$1 root $2"; done ) > out/cert_replay.txt
# Theorem 3.1 (no split rule), the original game, order 6
$P sweep.py $D/conn8.g6 0 4 > out/sweep8_np_k4.txt
$P sweep.py $D/conn8.g6 0 4 nonp > out/sweep8_nonp_k4.txt
grep ^LOSE out/sweep8_np_k4.txt | awk '{print $2}' > out/my47.g6
$P sweep.py out/my47.g6 5 9 all > out/least47_k5to9.txt
grep -v -F -x -f $O/dense7.g6 out/my47.g6 > out/sparse40.g6
$P sweep.py out/sparse40.g6 5 9 all split > out/least_sparse40_split.txt
$P sweep.py $O/np4_losers.g6 0 4 split > out/split47_k4.txt
$P sweep.py $O/losers5.g6 0 8 nonp all > out/losers5_nonp_k8.txt
$P sweep.py $O/losers5.g6 0 8 nonp split all > out/losers5_nonp_split_k8.txt
$P sweep.py $D/conn6.g6 0 4 nonp > out/conn6_nonp_k4.txt
$P k8pm.py 9 > out/k8pm.txt
$P gqz_original.py > out/gqz_original.txt
# criticality and endpoint-structure checks
$P partitions.py crit $O/np4_losers.g6 > out/crit47.txt
$P partitions.py ex53 > out/ex53.txt
$P es7_checks.py > out/es7_checks.txt
# order 10
./hubruns.sh > out/hubruns.txt
( $P hubrun.py 'I~{Nfbo{?' 0 2; $P hubrun.py 'I~~~~~_F?' 0 1 ) > out/hubruns_A44_B.txt
./rf_checks.sh > out/rf_checks.txt
$P rf_check.py 'Inv~|~zbw' 2 > out/rf_inv.txt

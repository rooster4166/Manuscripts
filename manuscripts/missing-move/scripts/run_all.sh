#!/bin/bash
# Reproduce the computations of the missing-move manuscript. Run from this directory.
# Needs python3 with networkx (and ortools for rootcheck.py). Data: ../../../data/conn8.g6.
# Times are for a 4-core machine; the n = 8 sweep at |F| <= 4 takes a few minutes, the
# reruns with |F| = 5..8 and the order-10 families take about an hour each.
set -e
D=$(dirname "$0"); O=$D/outputs; C8=$D/../../../data/conn8.g6
# Theorem 3.1: completeness at order 8 with path insertion
python3 $D/fan_game.py $C8 4 np > $O/sweep8_np4.log              # 47 graphs lose with |F| <= 4
grep LOSE $O/sweep8_np4.log | awk '{print $2}' > $O/np4_losers.g6
$D/stepper.sh $O/np4_losers.g6 np > $O/step_np.log                # the 40 sparser ones win with |F| in {5,6}
python3 $D/orbit_run.py $O/dense7.g6 5 8 np > $O/dense7_orbits.log # the 7 dense ones (6, 7, 8; K8-PM: see below)
# Proposition 4.3: Posa moves repair no losing root
python3 $D/fan_game.py $O/losers5.g6 4 rot2 > $O/rot2_k4.log
python3 $D/fan_game.py $O/losers5.g6 4 alt2 > $O/alt2_k4.log
python3 $D/fan_game.py $O/losers5.g6 6 alt1 > $O/alt1_k6.log
# certificates for the five losers (Remark 2.4)
for gr in "GsRvnk 2" "GsRvnk 3" "GsZvnk 4" "Gqrvn[ 2" "Gqzvn[ 4" "Gqzl|{ 1"; do
  set -- $gr; echo "=== $1 root $2"; python3 $D/certificate.py "$1" $2 6; done > $O/certificates.txt
# Section 5: order-10 families (hub-shaped held sets: a full star plus k edges)
(cd $O && python3 ../families.py)
for g in A44 A62 B B2; do for k in 0 1 2; do
  echo "$g k=$k: $(python3 $D/fan_game.py $O/$g.g6 $k np hubs | tail -1)"; done; done > $O/fam_np.log
# independent CP-SAT check of the rooted test
python3 $D/rootcheck.py $O/losers5.g6 $O/A62.g6 $O/B.g6 $O/B2.g6 > $O/rootcheck.log
# K8 minus a perfect matching: every held set of size 8 loses, the star plus three edges wins
python3 $D/single_root.py 'Gr~v~w' 0 8 > $O/k8pm.log
python3 $D/certificate.py 'Gr~v~w' 0 9 'F=((0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4),(2,4))' > $O/certificate_K8M.txt
# order 10 with a star plus three held edges, one root per orbit (run from outputs/, where the .g6 files are)
(cd $O && python3 ../fam_hub34.py A62 3 > famhub_A62_3.log && python3 ../fam_hub34.py B2 3 > famhub_B2_3.log)
python3 $D/certificate.py 'I~~~wF{~G' 0 10 'F=((0,1),(0,2),(0,6),(1,2),(1,6),(2,6),(3,6),(4,6),(5,6),(6,7))' > $O/certificate_B2.txt
# criticality (p < n/2 ?) of the 47 losers and of the test graphs
(cd $O && python3 ../crit.py np4_losers.g6 > crit47.log)
# Corollary 2.6: the critical loser Gqz~vw at root 3
python3 $D/certificate.py 'Gqz~vw' 3 5 > $O/certificate_Gqz.txt
# Proposition 5.8: the flower move on CP(4), CP(5), the order-10 families, the dense graphs, a sample
(for f in cp4 cp5; do for o in "0 hubs" "0 flower hubs" "0 np hubs" "0 np flower hubs"; do
  echo "$f [$o]: $(python3 $D/fan_game.py $O/$f.g6 $o | tail -1)"; done; done) > $O/cp_flower.log
(cd $O && for g in A62 B2; do for k in 0 1; do echo "$g k=$k: $(python3 ../fan_game.py $g.g6 $k np flower hubs | tail -1)"; done; done > fam_flower.log)
python3 $D/fan_game.py $O/dense7.g6 6 np flower > $O/dense7_flower6.log
(cd $O && python3 ../sample10.py 7 5 > sample10.g6)   # five critical order-10 graphs with a degree-6 vertex

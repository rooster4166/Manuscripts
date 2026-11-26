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
$D/stepper.sh $O/np4_losers.g6 np > $O/step_np.log                # each wins with |F| in {5,6}
python3 $D/orbit_run.py $O/dense7.g6 5 8 np > $O/dense7_orbits.log # the 7 dense ones, per root orbit
# Proposition 4.3: Posa moves repair no losing root
python3 $D/fan_game.py $O/losers5.g6 4 rot2 > $O/rot2_k4.log
python3 $D/fan_game.py $O/losers5.g6 4 alt2 > $O/alt2_k4.log
python3 $D/fan_game.py $O/losers5.g6 6 alt1 > $O/alt1_k6.log
# certificates for the five losers (Remark 2.4)
for gr in "GsRvnk 2" "GsRvnk 3" "GsZvnk 4" "Gqrvn[ 2" "Gqzvn[ 4" "Gqzl|{ 1"; do
  set -- $gr; echo "=== $1 root $2"; python3 $D/certificate.py "$1" $2 6; done > $O/certificates.txt
# Section 5: order-10 families (hub-shaped held sets: a full star plus k edges)
python3 $D/families.py
for g in A44 A62 B B2; do for k in 0 1 2; do
  echo "$g k=$k: $(python3 $D/fan_game.py $g.g6 $k np hubs | tail -1)"; done; done > $O/fam_np.log
# independent CP-SAT check of the rooted test
python3 $D/rootcheck.py $O/losers5.g6 A62.g6 B.g6 B2.g6 > $O/rootcheck.log

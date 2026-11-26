#!/bin/sh
# Re-runs every check of d6-frontier.tex and stores the outputs (*.out).  Low priority.
set -e
cd "$(dirname "$0")"
N="nice -n 15"
$N python3 test_engine.py 1 > test_engine.out; $N python3 test_engine.py 2 >> test_engine.out
$N python3 terminal_check.py > terminal_check.out
$N python3 replay_root_hub.py 1 4 12 > replay_root_hub.out
$N python3 replay_root_hub.py 10 3 12 2 >> replay_root_hub.out
$N python3 replay_root_hub.py 20 3 14 1 >> replay_root_hub.out
for sh in K2 P3 K3 C4; do $N python3 replay_shapes.py $sh 1 2 12; done > replay_shapes.out
$N python3 replay_two_resources.py 1 4 14 > replay_two_resources.out
$N python3 replay_relay.py 1 3 12 1 > replay_relay.out
$N python3 replay_relay.py 7 2 14 2 >> replay_relay.out
$N python3 replay_full_hub.py 1 3 14 > replay_full_hub.out
$N python3 replay_general_d.py root 1 2 16 8 > replay_general_d.out
$N python3 replay_general_d.py full 1 1 16 8 >> replay_general_d.out
$N python3 stage_search.py fullpair > stage_search.out
$N python3 small_observation.py > small_observation.out
echo "all checks completed"

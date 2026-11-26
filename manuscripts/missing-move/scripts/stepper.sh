#!/bin/bash
# usage: stepper.sh FILE OPTS... ; for each graph, raise kmax from 5 to 8 until it has no losing root
f=$1; shift
while read -r g; do
  echo "$g" > "${TMPDIR:-/tmp}"/step_$$.g6
  res="LOSE"
  for k in 5 6 7 8; do
    out=$( (ulimit -v 6000000; timeout 1800 nice -n 12 python3 "$(dirname "$0")"/fan_game.py "${TMPDIR:-/tmp}"/step_$$.g6 $k "$@") 2>&1 | tail -1)
    if echo "$out" | grep -q " 0 with a losing root"; then res="WIN k=$k"; break; fi
    if ! echo "$out" | grep -q "with a losing root"; then res="ERR k=$k $out"; break; fi
  done
  echo "$g $res" 
done < "$f"
echo DONE

#!/bin/bash
# For each graph: the least k (held set = a full star plus k edges) at which the game wins every
# root, with and without receipt-or-flower (both with path insertion and the orbit rule).
D=$(dirname "$0")
while read -r g; do
  echo "$g" > "${TMPDIR:-/tmp}"/rf_$$.g6
  for opt in "np rf orbit hubs" "np orbit hubs"; do
    res="LOSE k<=2"
    for k in 0 1 2; do
      out=$( (ulimit -v 5000000; timeout 2400 nice python3 $D/fan_game.py "${TMPDIR:-/tmp}"/rf_$$.g6 $k $opt) 2>&1 | tail -1)
      if echo "$out" | grep -q " 0 with a losing root"; then res="WIN k=$k"; break; fi
    done
    echo "$g [$opt]: $res"
  done
done < "$1"
echo DONE

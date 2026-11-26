#!/bin/bash
# Exhaustive runs used in the computational appendix.
cd "$(dirname "$0")"
out=../data
for args in "7 4 3 0" "7 3 4 0" "7 2 4 0" "7 5 2 0" "8 4 3 0" "8 3 4 0" "8 5 2 0" "8 2 5 0"; do
  f=$out/exh_$(echo $args | tr ' ' _).txt
  [ -s "$f" ] && grep -q SUMMARY "$f" && continue
  ./flower $args > "$f" 2>/dev/null
done

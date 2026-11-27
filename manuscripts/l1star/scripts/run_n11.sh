#!/bin/sh
# Exhaustive order 11 for the local form (three geng slices, in parallel).
cd "$(dirname "$0")"
for i in 0 1 2; do (nauty-geng -cq 11 $i/3 | ./l1s max 3 > out/max11_$i.txt 2> out/max11_$i.err) & done
wait

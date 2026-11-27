#!/bin/bash
# random multigraph-case tests (Conjecture 2.4): G' 2-connected, all pairings of Ev(G')
cd "$(dirname "$0")"
for n in 10 12 14; do for M in 2 3; do
  python3 gen_multi.py $n $M 120 $((n*10+M)) 2conn > out/multi_${n}_${M}.g6
  nice -n 10 ./ptm p $M 200000 0 < out/multi_${n}_${M}.g6 > out/multi_${n}_${M}.out
  echo "$n $M $(tail -1 out/multi_${n}_${M}.out)"
done; done

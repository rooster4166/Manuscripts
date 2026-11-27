#!/bin/bash
# queued experiments: cubic graphs n = 12, 14 (PTM_2, PTM(e@x), up to isomorphism); walk-base reach with longer walks
cd "$(dirname "$0")"
for n in 12 14; do
  nauty-geng -cq -d3 -D3 $n | ./encode 2 | nauty-labelg -q | sort -u | python3 decode.py > out/cubic_${n}_2.in
  nice -n 10 ./ptm f 2 2000000 0 < out/cubic_${n}_2.in > out/cubic_${n}_2.out
  echo "cubic $n $(wc -l < out/cubic_${n}_2.in) $(tail -1 out/cubic_${n}_2.out)"
done
nice -n 10 ./walk 2 0 < out/pairs_8.txt > out/walk_8_2.txt; echo "walk extra=2: $(tail -1 out/walk_8_2.txt)"

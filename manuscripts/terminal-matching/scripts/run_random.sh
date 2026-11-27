#!/bin/bash
cd "$(dirname "$0")"
for n in 12 14 16; do for m in 2 3 4; do for mode in rand close share; do
  python3 gen_random.py $n $m 150 $((n*100+m*10)) $mode > out/rnd_${n}_${m}_${mode}.in
  nice -n 10 ./ptm f $m 200000 0 < out/rnd_${n}_${m}_${mode}.in > out/rnd_${n}_${m}_${mode}.out
  echo "$n $m $mode $(tail -1 out/rnd_${n}_${m}_${mode}.out)"
done; done; done

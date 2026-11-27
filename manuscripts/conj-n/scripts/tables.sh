#!/bin/bash
# tables.sh: the closure table of the manuscript (Section 6).  Output: out/tables.txt
# Orders 5, 7 for every class (all A, B as the class allows); order 9 for the B-free classes.
set -e
O=../../stl/scripts
run() { # class flags order
  local C=$1 F=$2 n=$3 src
  if [ $n -le 8 ]; then src="nauty-geng -cq $n"; else src="cat $O/one_even_$n.g6"; fi
  echo "n=$n class=$C flags=[$F] $($src | ./closure2 $C $F -p 0 | tail -1)"
}
{
for n in 5 7; do
  for C in N1 N2 V U L1 C1; do run $C "-s -b 0" $n; done
  for C in N2B NBA W N2XC; do run $C "-s" $n; done
  run D_N2 "-s -b 0 -D 3" $n
  for C in N1 N2; do run $C "-T -b 0" $n; done
  for C in N1 N2 N1NA C1; do run $C "-T2 -b 0" $n; done
done
for n in 6 8; do for C in N1NA C1; do run $C "-T2 -b 0" $n; done; done
for C in N1 N2; do run $C "-b 0" 9; done
for C in N1 N1NA; do run $C "-T2 -b 0" 9; done
} > out/tables.txt 2>&1
# subcubic graphs (all degrees <= 3), appended to data/tables.txt by hand:
# for n in 5 7 9; do nauty-geng -cq -D3 $n | ./closure2 D_N2 -D 3 -G 2 -s -b 0 -p 0 | tail -1; done

#!/bin/sh
# classify9.sh: (G, D') classification on the first 4000 graphs of one_even_9.g6 (the sparser ones),
# skipping tests with more than 20000 good D'; 4 parallel parts.  Takes a few hours.
O=../../stl/scripts; D=../data
head -4000 $O/one_even_9.g6 > /tmp/trn_o9a.g6; split -n r/4 -d /tmp/trn_o9a.g6 /tmp/trn_o9a_
for i in 0 1 2 3; do ./classify 20 20000 < /tmp/trn_o9a_0$i > /tmp/trn_cls9a_$i.txt & done; wait
cat /tmp/trn_cls9a_*.txt > $D/classify9_first4000.txt

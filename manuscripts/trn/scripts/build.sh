#!/bin/sh
# build.sh: compile the C++ tools (the oracle headers lind.h, orc2.h, dec.h are in ../../l1-induction/scripts)
set -e
I=../../l1-induction/scripts
for t in chain chainlist classify core rules minchain trne trnbud show clean rot halves local steer steer2; do
  g++ -O2 -I $I -o $t $t.cpp
done

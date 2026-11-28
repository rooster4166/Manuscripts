#!/bin/bash
# A37b item 4: reproduce slack witnesses with t2.c -s and verify_t2.py --require-slack
cd "$(dirname "$0")"
V=../../../manuscripts/test2/scripts/verify_t2.py
for n in 6 8; do
  echo "## order $n"
  ( nauty-geng -q -C -d3 $n | ./t2 -s > t2_s_$n.out ) 2>&1
  python3 $V --require-slack < t2_s_$n.out
done
echo "## order 10, slice 0/40"
( time (nauty-geng -q -C -d3 10 0/40 | ./t2 -s > t2_s_10_0of40.out) ) 2>&1
python3 $V --require-slack < t2_s_10_0of40.out

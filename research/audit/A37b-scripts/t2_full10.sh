#!/bin/bash
# A37b item 4: the full order-10 run of t2.c -s, verified with verify_t2.py --require-slack
cd "$(dirname "$0")"
V=../../../manuscripts/test2/scripts/verify_t2.py
( time (nauty-geng -q -C -d3 10 | ./t2 -s > t2_s_10_full.out) ) 2>&1
( time python3 $V --require-slack < t2_s_10_full.out ) 2>&1

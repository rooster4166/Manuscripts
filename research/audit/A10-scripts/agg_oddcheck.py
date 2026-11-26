"""Odd k: does the counting relaxation of Prop LH survive one extra S colour (2|U| <= k-1)?"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import agg_smax_plus1 as A
bad = [(k,) + A.check(k) for k in range(5, 100, 2) if min(A.check(k)) < 0]
print("odd k 5..99 with 2|U| <= k-1: failures", bad)

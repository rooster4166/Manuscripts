"""aeq.py -- queries for AE (avoid the even vertex): from 'g6 c1 a1 c2 a2 ci ai cj aj' lines with
c_i a leaf at a_j: the graph F - c_i (one even vertex a_j) with 'A c_j a_j'."""
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode, g6_encode
for line in sys.stdin:
    t = line.split()
    if not t: continue
    n, adj = g6_decode(t[0]); ci, ai, cj, aj = map(int, t[5:9])
    A = [set(a) for a in adj]; A[ci].discard(aj); A[aj].discard(ci)
    print(g6_encode(n, A), 'A', cj, aj)

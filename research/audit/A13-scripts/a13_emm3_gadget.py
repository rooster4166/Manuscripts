#!/usr/bin/env python3
"""Audit A13: the forcing property behind the order-18 EMM_3 counterexample, by the A13 oracle.
D = two K4 blocks {a0..a3}, {b0..b3} plus p ~ a1, a2, b1 and q ~ a3, b2, b3.
  D+ = D + leaves l1 at p, l2 at b0, with b = 1 at l1, l2, a0, q: realisable (2 paths).
  D + w, w ~ p, b0, with b(w) = 2, b = 1 at a0, q: NOT realisable. So every realisation of D+
  joins l1 to l2 by one path, which in the host would be a closed walk through s.
  D + w with b(w) = 0: not realisable either (one path cannot cover a degree-4 vertex).
With the 2-edge cut {sp, sb0} these give the gluing argument of synthesis §14."""
import itertools
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a13_realis import realisable  # noqa: E402

a0, a1, a2, a3, b0, b1, b2, b3, p, q = range(10)
D = nx.Graph()
D.add_edges_from(itertools.combinations([a0, a1, a2, a3], 2))
D.add_edges_from(itertools.combinations([b0, b1, b2, b3], 2))
D.add_edges_from([(p, a1), (p, a2), (p, b1), (q, a3), (q, b2), (q, b3)])
Dp = D.copy(); Dp.add_edges_from([(p, 10), (b0, 11)])
b = [0] * 12; b[a0] = b[q] = b[10] = b[11] = 1
print('D+ (leaves at p, b0) realisable:', realisable(Dp, b))
Dw = D.copy(); Dw.add_edges_from([(p, 10), (b0, 10)])
bw = [0] * 11; bw[a0] = bw[q] = 1; bw[10] = 2
print('D + w, b(w) = 2 realisable:', realisable(Dw, bw))
bw[10] = 0
print('D + w, b(w) = 0 realisable:', realisable(Dw, bw))

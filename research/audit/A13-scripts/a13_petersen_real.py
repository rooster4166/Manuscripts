#!/usr/bin/env python3
"""Audit A13: realisability of the gadget half-set of G(Petersen) (n = 28) by the A13 oracle,
a direct check of the non-realisable direction of Prop 25 / Thm 27 (expected: False)."""
import os
import random
import sys
import time

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a13_check as C  # noqa: E402
from a13_kotzig import build  # noqa: E402
from a13_realis import realisable  # noqa: E402

for name, H in (('prism', nx.circular_ladder_graph(3)), ('cube', nx.hypercube_graph(3)),
                ('Petersen', nx.petersen_graph())):
    G, gad, LG, E = build(H, random.Random(1))
    deg = [G.degree(v) for v in G]
    t = time.time()
    print(name, 'n =', G.number_of_nodes(), 'gadget realisable:', realisable(G, C.simple_profile(deg, gad)),
          '[%.0fs]' % (time.time() - t), flush=True)

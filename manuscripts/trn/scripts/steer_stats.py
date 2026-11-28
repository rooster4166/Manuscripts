#!/usr/bin/env python3
"""steer_stats.py: statistics of the CORE lines of `SHOWCORE=1 ./steer2 CORETESTS ...`, one line per
core triple (G, y, x) (a triple with at least one core test).  Counts the triples with and without a
two-token schedule, those with N(y) inside N[g] (no legal first move, Proposition 6.10), and checks
that every schedule starts with a move of the y-token (also Proposition 6.10).
usage: SHOWCORE=1 ./steer2 CORETESTS 2000000 0 0 < graphs.g6 | python3 steer_stats.py"""
import sys
sys.path.insert(0, '.')
from brute import parse_g6
tot = sch = uns = stuck_u = stuck_s = firsty = 0
for l in sys.stdin:
    if not l.startswith('CORE'): continue
    p = l.split()
    n, adj = parse_g6(p[1])
    g, y, s = int(p[2][2:]), int(p[3][2:]), int(p[5][6:])
    stuck = all(q == g or q in adj[g] for q in adj[y])
    tot += 1
    if s == 1:
        sch += 1; stuck_s += stuck; firsty += p[7].startswith('1:')
    else:
        uns += 1; stuck_u += stuck
print(f'core triples {tot}: schedule {sch} (first move by the y-token in {firsty}; with N(y) in N[g] {stuck_s}), '
      f'no schedule {uns} (with N(y) in N[g] {stuck_u})')

"""Exhaustive check of the validity lemma (V1)-(V4) on small instances: for each
instance (Q on K_m, colour c) enumerate ALL colourings chi of the 2m new edges
(xy gets colour c) and compare graph-level validity with conditions (V1)-(V4)."""
import itertools, random, sys
from lf import components, edges_by_colour, is_linear_forest
from solvers import one_vertex_step

def conditions(m, n, col, c, cx, cy):
    E = edges_by_colour(m, n, col)
    deg = [[0] * m for _ in range(n)]
    for i in range(n):
        for u, v in E[i]: deg[i][u] += 1; deg[i][v] += 1
    for i in range(n):
        for v in range(m):
            if (cx[v] == i) + (cy[v] == i) > 2 - deg[i][v]: return False      # V1
        if sum(cx[v] == i for v in range(m)) > 2 - (i == c): return False     # V2
        if sum(cy[v] == i for v in range(m)) > 2 - (i == c): return False
        both = 0
        for (u, w) in components(m, E[i]):
            ends = {u, w}
            dx = sum(cx[v] == i for v in ends); dy = sum(cy[v] == i for v in ends)
            if dx > 1 or dy > 1: return False                                  # V3
            if dx >= 1 and dy >= 1: both += 1
        if both > (0 if i == c else 1): return False                           # V4
    return True

def graph_valid(m, n, col, c, cx, cy):
    new = dict(col); x, y = m, m + 1
    for v in range(m): new[(v, x)] = cx[v]; new[(v, y)] = cy[v]
    new[(x, y)] = c
    E = edges_by_colour(m + 2, n, new)
    return all(is_linear_forest(m + 2, E[i]) for i in range(n))

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
tot = agree = valid = 0
for trial in range(int(sys.argv[2]) if len(sys.argv) > 2 else 12):
    n = rng.randint(2, 4); m = rng.randint(1, min(4, 2 * n - 1))
    col = {}
    for mm in range(1, m): col = one_vertex_step(mm, n, col, rng)
    c = rng.randrange(n)
    for cx in itertools.product(range(n), repeat=m):
        for cy in itertools.product(range(n), repeat=m):
            a = conditions(m, n, col, c, cx, cy); b = graph_valid(m, n, col, c, cx, cy)
            tot += 1; agree += (a == b); valid += b
print("colourings", tot, "agree", agree, "valid", valid)

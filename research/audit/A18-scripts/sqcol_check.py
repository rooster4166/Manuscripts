import sys, random, subprocess
sys.path.insert(0, "/home/user/Manuscripts/manuscripts/multi-sep/scripts")
from exp_sqcol import square, colour
from g6 import g6_to_adj
rng = random.Random(1)
for n in (10, 12, 14):
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {n}", shell=True, capture_output=True, text=True).stdout.split()
    bad = 0
    for s in gs:
        K = g6_to_adj(s); Sq = square(K)
        start = max(len(Sq[v]) for v in Sq) // 2 + 1
        k = 4  # Delta+1 lower bound for cubic
        while not colour(Sq, k, rng): k += 1
        if k < start: bad += 1
    print(n, len(gs), "graphs with chi(K^2) < start value of min_colouring:", bad)

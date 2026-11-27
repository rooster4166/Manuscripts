import sys, random, subprocess
sys.path.insert(0, "/home/user/Manuscripts/manuscripts/multi-sep/scripts")
import msl
from g6 import g6_to_adj
rng = random.Random(7)
lines = subprocess.run("nauty-geng -cq -d3 -D3 10", shell=True, capture_output=True, text=True).stdout.split()
queries = []
for s in lines:
    K = g6_to_adj(s)
    for _ in range(15):
        pairs = msl.far_pairs(K, rng, mind=rng.choice([2, 2, 3]))
        k = rng.randint(1, len(pairs)) if pairs else 0
        queries.append((s, K, pairs[:k]))
inp = "".join(f"{s} {len(p)} " + " ".join(f"{a} {b}" for a, b in p) + "\n" for s, K, p in queries)
out = subprocess.run([sys.argv[1], "given"], input=inp, capture_output=True, text=True).stdout.split()
for (s, K, p), r in zip(queries, out):
    if r == '0':
        print(s, "min pair distance", min(msl.dist(K, a)[b] for a, b in p))

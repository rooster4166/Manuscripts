"""Cross-check cubsep mode `classes` against the exact oracle (query S with all pairs inside each
class) on cubic graphs of order 10 and 12, using random colourings with few colours (often not proper
for the square, so failures occur) and minimum square colourings."""
import random, subprocess
import msl, oracle
from g6 import g6_to_adj
from exp_sqcol import min_colouring
rng = random.Random(3)
qs = []
for n in (10, 12):
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {n}", shell=True, capture_output=True, text=True).stdout.split()
    for s in rng.sample(gs, min(15, len(gs))):
        K = g6_to_adj(s)
        for _ in range(4):
            k = rng.choice([3, 4, 5, 6])
            col = [rng.randrange(k) for _ in range(n)]
            qs.append((s, K, col))
        k, c = min_colouring(K, rng)
        qs.append((s, K, [c[v] for v in range(n)]))
out = subprocess.run(["./cubsep", "classes"], input="".join(s + " " + " ".join(map(str, col)) + "\n" for s, K, col in qs), capture_output=True, text=True).stdout.splitlines()
agree = dis = fails = 0
results = [0 if l.startswith("FAIL") else None for l in out[:-1]]
# cubsep prints only FAIL lines and a summary; rebuild per-query answers by running one at a time
for s, K, col in qs:
    r = subprocess.run(["./cubsep", "classes"], input=s + " " + " ".join(map(str, col)) + "\n", capture_output=True, text=True).stdout
    c_ans = 0 if "FAIL" in r else 1
    pairs = [(a, b) for a in range(len(col)) for b in range(a + 1, len(col)) if col[a] == col[b]]
    o_ans = oracle.query("S", K, msl.lovasz_profile(K), sep=pairs)
    if c_ans == o_ans: agree += 1
    else: dis += 1; print("DISAGREE", s, col, c_ans, o_ans)
    fails += (o_ans == 0)
print("agree", agree, "disagree", dis, "oracle failures", fails)

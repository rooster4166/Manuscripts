"""Cross-check cubsep.c against the independent Python enumerator msl.all_decomps
(all connected cubic graphs of order 10, random pairings at distance >= 2 or >= 3)."""
import random, subprocess
import msl
from g6 import g6_to_adj

def main():
    rng = random.Random(7)
    lines = subprocess.run("nauty-geng -cq -d3 -D3 10", shell=True, capture_output=True,
                           text=True).stdout.split()
    queries = []
    for s in lines:
        K = g6_to_adj(s)
        for _ in range(15):
            pairs = msl.far_pairs(K, rng, mind=rng.choice([2, 2, 3]))
            k = rng.randint(1, len(pairs)) if pairs else 0
            queries.append((s, K, pairs[:k]))
    inp = "".join(f"{s} {len(p)} " + " ".join(f"{a} {b}" for a, b in p) + "\n"
                  for s, K, p in queries)
    out = subprocess.run(["./cubsep", "given"], input=inp, capture_output=True,
                         text=True).stdout.split()
    agree = dis = 0
    for (s, K, p), r in zip(queries, out):
        py = 1 if msl.all_decomps(K, msl.lovasz_profile(K), limit=1, pairs=p) else 0
        if py == int(r):
            agree += 1
        else:
            dis += 1
            print("DISAGREE", s, p, r, py)
    res = out[:len(queries)]   # one result per query; the summary line follows
    print("agree", agree, "disagree", dis, "fails", sum(1 for r in res if r == '0'))

if __name__ == "__main__":
    main()

"""All connected cubic graphs of order n: a minimum proper colouring of the square for each, and
CSEP checked by cubsep (mode classes).  Optionally several random minimum colourings per graph."""
import random, subprocess, sys
from g6 import g6_to_adj
from exp_sqcol import min_colouring

def main(n, per, seed):
    rng = random.Random(seed)
    gs = subprocess.run(f"nauty-geng -cq -d3 -D3 {n}", shell=True, capture_output=True, text=True).stdout.split()
    lines = []
    from collections import Counter
    kc = Counter()
    for s in gs:
        K = g6_to_adj(s)
        for _ in range(per):
            k, c = min_colouring(K, rng)
            kc[k] += 1
            lines.append(s + " " + " ".join(str(c[v]) for v in range(n)))
    out = subprocess.run(["./cubsep", "classes"], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout
    print(f"n={n}: graphs {len(gs)}, colourings {len(lines)}, colours used {dict(sorted(kc.items()))}")
    print(out.strip().splitlines()[-1])
    fails = [l for l in out.splitlines() if l.startswith("FAIL")]
    for f in fails[:5]: print(f)
if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))

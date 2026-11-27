"""exact_part.py -- audit A21: exact results of an interrupted exhaust.py run, up to its last
PROGRESS checkpoint.  A PROGRESS line with 'graphs': N is printed before graph N is processed, so it
holds the exact counts for graphs 1..N-1; the AWAYFAIL lines before it are those graphs' failures.

usage: python3 exact_part.py LOG  -> prints the checkpoint counts and writes LOG.fails"""
import sys, ast
lines = open(sys.argv[1]).read().splitlines()
last = max(i for i, l in enumerate(lines) if l.startswith("PROGRESS"))
C = ast.literal_eval(lines[last][len("PROGRESS "):])
fails = [l for l in lines[:last] if l.startswith("AWAYFAIL")]
assert len(fails) == C.get("away:fail", 0), (len(fails), C)
print(sys.argv[1], "checkpoint: graphs processed =", C["graphs"] - 1, C)
with open(sys.argv[1] + ".fails", "w") as fh:
    for l in fails:
        p = l.split()
        fh.write(f"{p[1]} {p[3]} {p[4]}\n")

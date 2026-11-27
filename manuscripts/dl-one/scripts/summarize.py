"""summarize.py: count DL(1) outcomes in dl.c output (pairs or core mode)."""
import sys
from collections import Counter
C = Counter()
for line in open(sys.argv[1]):
    if "skip" in line:
        C["skip"] += 1
        continue
    parts = line.split(";")
    C["graphs"] += 1
    for item in parts[2].split(","):
        f = item.split()
        if len(f) < 5:
            continue
        a, b, ob, oa, tw = map(int, f[:5])
        C["pairs"] += 1
        ok = ob or oa
        if not ok:
            C["fail"] += 1
        if tw:
            C["twins"] += 1
        if (not ok) != bool(tw):
            C["MISMATCH"] += 1
            print("MISMATCH", parts[0].strip(), a, b, ob, oa, tw)
        if ob and oa:
            C["both"] += 1
        elif ok:
            C["one"] += 1
print(dict(C))

"""compare.py A B: compare per-pair (ob, oa) between two outputs (dl.c and brute.py)."""
import sys
def load(fn):
    D = {}
    for line in open(fn):
        if "skip" in line or "toolarge" in line:
            continue
        p = line.split(";")
        g6 = p[0].strip()
        for item in p[2].split(","):
            f = item.split()
            if len(f) >= 4 and f[0].isdigit():
                D[(g6, int(f[0]), int(f[1]))] = (int(f[2]), int(f[3]))
    return D
A, B = load(sys.argv[1]), load(sys.argv[2])
common = set(A) & set(B)
bad = [k for k in common if A[k] != B[k]]
print("compared", len(common), "mismatches", len(bad), "onlyA", len(set(A) - set(B)), "onlyB", len(set(B) - set(A)))
for k in bad[:10]:
    print(k, A[k], B[k])

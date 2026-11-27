"""compare_z.py P_FILE RETZ_FILE: compare ret.c -z with re.c -p.

ret.c -z decides, at a root r of degree n - 2, whether B has a decomposition into k - 1 paths all
through r; that holds iff p(B) <= k - 1 (each of k - 1 paths uses at most two of the 2k - 2 edges
at r, so all of them pass through r).  re.c -p prints p(B) ('g6 -1 p k status').
Every ret.c answer (YES/NO) must agree with [p(B) <= k - 1]; UNK lines, and graphs whose p(B)
re.c left undecided, are counted separately.
"""
import sys

p = {}
for line in open(sys.argv[1]):
    g6, rest = line.split(None, 1)
    f = rest.split()
    if f[3] != "OK":  # re.c left p(B) undecided at its budget
        continue
    p[g6] = (int(f[1]), int(f[2]))
agree = disagree = unk = 0
yes = no = 0
for line in open(sys.argv[2]):
    g6, rest = line.split(None, 1)
    f = rest.split()
    st = f[1]
    if g6 not in p:
        unk += 1
        continue
    pb, k = p[g6]
    if st == "UNK":
        unk += 1
        continue
    want = pb <= k - 1
    got = st == "YES"
    yes += got
    no += not got
    if want == got:
        agree += 1
    else:
        disagree += 1
        print("DISAGREE", g6, f[0], st, "p(B) =", pb)
print("roots: %d agree (%d YES, %d NO), %d disagree, %d UNK" % (agree, yes, no, disagree, unk))
sys.exit(1 if disagree else 0)

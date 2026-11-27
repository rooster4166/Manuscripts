"""compare_bf.py BF_OUT RE_X_OUT RE_P_OUT: compare bf.py with re.c -x (rooted) and re.c -p."""
import sys


def rd_bf(fn):
    d = {}
    for l in open(fn):
        g, t = l.split(None, 1)
        a, b = t.rsplit("|", 1)
        d[g] = (list(map(int, a.split())), int(b))
    return d


def rd_re(fn):
    d = {}
    for l in open(fn):
        g, t = l.split(None, 1)
        f = t.split()
        d.setdefault(g, {})[int(f[0])] = int(f[1])
    return d


bf, rr, rp = rd_bf(sys.argv[1]), rd_re(sys.argv[2]), rd_re(sys.argv[3])
mm = tot = 0
for g, (pr, p) in bf.items():
    for r, v in enumerate(pr):
        tot += 1
        if rr[g].get(r, -1) != v:
            mm += 1
            print("MISMATCH", g, r, v, rr[g].get(r))
    tot += 1
    if rp[g][-1] != p:
        mm += 1
        print("MISMATCH p", g, p, rp[g][-1])
print("graphs", len(bf), "values compared", tot, "mismatches", mm)

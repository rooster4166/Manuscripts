"""cmp_lov.py LOVCHECK_OUT [RETT_FILE] [RETL_FILE]: compare lovcheck.c with ret.c -T / -L.

-T: number of Lovasz decompositions (ret's lovasz=) and minmu must agree on DONE roots.
-L: lovcheck's Lyes must agree with ret -L YES/NO on decided roots (only where lovcheck is DONE
    or LSTOP with Lyes = 1).
Also: Theorem 3.1 check with every tie-break: (**) => minmuA >= k - 3.
"""
import sys
from collections import Counter

sys.path.insert(0, __import__("os").path.dirname(__file__))
from g6 import parse_g6  # noqa: E402
from recount_conditions import star2  # noqa: E402


def main():
    lc = {}
    for line in open(sys.argv[1]):
        g, r, nd, mT, mA, Ly, st, need = line.split()
        lc[(g, int(r))] = (int(nd), int(mT), int(mA), int(Ly), st, int(need.split("=")[1]))
    c = Counter()
    for (g, r), (nd, mT, mA, Ly, st, need) in lc.items():
        n, adj = parse_g6(g)
        s2 = star2(n, adj, r)
        if st == "DONE":
            c[("thm", s2, mA >= need)] += 1
            if s2 and mA < need:
                print("THEOREM VIOLATION", g, r, mA, need)
    if len(sys.argv) > 2 and sys.argv[2] != "-":
        for line in open(sys.argv[2]):
            f = line.split()
            key = (f[0], int(f[1]))
            if key not in lc or f[2] != "DONE":
                c["T: skipped"] += 1
                continue
            nd, mT, mA, Ly, st, need = lc[key]
            if st != "DONE":
                c["T: lovcheck capped"] += 1
                continue
            lov = int(f[3].split("=")[1])
            mu = int(f[4].split("=")[1])
            if lov == nd and mu == mT:
                c["T: agree"] += 1
            else:
                c["T: DISAGREE"] += 1
                print("T DISAGREE", line.strip(), lc[key])
    if len(sys.argv) > 3:
        for line in open(sys.argv[3]):
            f = line.split()
            key = (f[0], int(f[1]))
            if key not in lc:
                c["L: skipped"] += 1
                continue
            nd, mT, mA, Ly, st, need = lc[key]
            if f[2] == "UNK":
                c[("L: ret UNK, lovcheck", st, Ly)] += 1
                continue
            if st == "CAP" and not Ly:
                c[("L: lovcheck CAP, ret", f[2])] += 1
                continue
            if (f[2] == "YES") == bool(Ly):
                c[("L: agree", f[2])] += 1
            else:
                c["L: DISAGREE"] += 1
                print("L DISAGREE", f[0], f[1], f[2], lc[key])
    for kk in sorted(c, key=str):
        print(kk, c[kk])


if __name__ == "__main__":
    main()

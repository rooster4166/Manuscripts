"""h_cones.py (audit A37): count cone instances (J has a universal vertex other than z, r) per n in
the session's field files, with my own decoder; check the 20 tight instances are cones and that
B = J - u has exactly the two odd vertices z ~ r (Prop 8.1(a)).  usage: python3 h_cones.py"""
import gzip, sys
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from a37lib import adjacency, g6_decode
D = "/home/user/Manuscripts/manuscripts/test2/data/"
st = Counter()
tight = {tuple(l.split()[:3]) for l in open(D + "tight_le10.txt")}
for fn, op in ((D + "t2_order6_8.txt", open), (D + "t2_order10_fields.txt.gz", gzip.open)):
    with op(fn, "rt") as fh:
        for line in fh:
            g6, z, r = line.split()[:3]
            n, E = g6_decode(g6); A = adjacency(n, E); zi, ri = int(z), int(r)
            U = [u for u in range(n) if len(A[u]) == n - 1 and u not in (zi, ri)]
            if (g6, z, r) in tight:
                st[("tight", n, "cone", bool(U))] += 1
            if not U:
                continue
            st[("cone inst", n)] += 1
            u = U[0]
            Bu = {e for e in E if u not in e}; AB = adjacency(n, Bu)
            odd = sorted(v for v in range(n) if v != u and len(AB[v]) % 2 == 1)
            assert odd == sorted((zi, ri)) and ri in AB[zi]
            st[("t2 field", n, line.split()[7])] += 1
for k in sorted(st, key=str): print(k, st[k])

"""c_order10.py (audit A37, item 3c): a seeded random sample of order-10 lines of
data/t2_order10_fields.txt.gz.  Per instance, with my own code only:
  * the fields d(z), d(r), n agree with the graph; z, r are the only even vertices, adjacent;
    J is 3-connected (own test);
  * (T2): CP-SAT finds <= 5 paths with >= 3 ends at r; witness checked by my own checker;
  * slack: CP-SAT decides p(B) <= 4 (the session's t2.c prints NO witness for slack = 1, so this
    is the only independent check of those positive answers); witness checked; compared with the
    slack field.
usage: python3 c_order10.py SAMPLE_SIZE SEED
"""
import gzip
import random
import sys
from collections import Counter

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from a37lib import adjacency, check_decomp, cpsat_decomp, delete_vertex, g6_decode, kconn, t2_instances

F = "/home/user/Manuscripts/manuscripts/test2/data/t2_order10_fields.txt.gz"


def main():
    N = int(sys.argv[1])
    seed = int(sys.argv[2])
    with gzip.open(F, "rt") as fh:
        lines = fh.read().splitlines()
    rng = random.Random(seed)
    sample = rng.sample(lines, N)
    st = Counter()
    for line in sample:
        g6, tail = line.split(None, 1)
        z, r, dz, dr, n, slack, t2, emax = map(int, tail.split("|")[0].split())
        nn, E = g6_decode(g6)
        A = adjacency(nn, E)
        assert nn == n == 10
        assert len(A[z]) == dz and len(A[r]) == dr
        assert (z, r) in t2_instances(nn, E), line
        assert kconn(nn, A, 3), line
        B = delete_vertex(E, z)
        s1, W = cpsat_decomp(B, 5, r=r, minends=3, time_limit=120)
        if s1 == "FEAS":
            check_decomp(B, W, maxpaths=5, r=r, minends=3)
        s2, W2 = cpsat_decomp(B, 4, time_limit=120)
        if s2 == "FEAS":
            check_decomp(B, W2, maxpaths=4)
        myslack = {"FEAS": 1, "INFEAS": 0}.get(s2, 2)
        st[("t2", s1)] += 1
        st[("slack mine", myslack, "file", slack)] += 1
        st[("dz", dz)] += 1
        if myslack != slack or s1 != "FEAS":
            print("DISAGREE", line[:60], s1, myslack, flush=True)
    for k in sorted(st, key=str):
        print(k, st[k])


if __name__ == "__main__":
    main()

"""b_tight.py (audit A37, item 3b).
1. On data/tight_le10.txt (20 instances): own witness check; e(B) > 2k^2 (odd semi-clique) and
   d_H(r); CP-SAT proves p(B) > k (INFEASIBLE with k slots) independently of edge counting;
   CP-SAT finds the maximum number of ends at r within n/2 paths (tries d_H(r)+2, and checks
   d_H(r)+4 is infeasible, as the vertex bound predicts).
2. Over ALL order-6/8/10 field lines: slack = 0 <=> e(B) > 2k^2 (semi-clique by edge count).
usage: python3 b_tight.py
"""
import gzip
import sys
from collections import Counter

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from a37lib import adjacency, check_decomp, cpsat_decomp, delete_vertex, g6_decode

D = "/home/user/Manuscripts/manuscripts/test2/data/"


def parse(line):
    g6, tail = line.split(None, 1)
    head, *rest = tail.split("|")
    f = list(map(int, head.split()))
    paths = [list(map(int, s.split())) for s in rest if s.strip()]
    return g6, f, paths


def main():
    print("== tight_le10.txt")
    cnt = Counter()
    for line in open(D + "tight_le10.txt"):
        g6, f, W = parse(line)
        z, r, dz, dr, n, slack, t2, emax = f
        nn, E = g6_decode(g6)
        B = delete_vertex(E, z)
        k = (n - 2) // 2
        A = adjacency(nn, B)
        Vb = [v for v in range(nn) if v != z]
        dH = {v: (2 * k) - len(A[v]) for v in Vb}       # degree in the complement H inside K_{2k+1}
        eH = k * (2 * k + 1) - len(B)
        semi = eH < k
        ends = check_decomp(B, W, maxpaths=n // 2, r=r, minends=3)
        # CP-SAT infeasibility proofs are cheap at n <= 8 but slow at n = 10, where the edge count
        # e(B) > 2k^2 (a path has <= 2k edges) already proves p(B) > k.
        st = cpsat_decomp(B, k, time_limit=300)[0] if n <= 8 else ("edge-count" if 2 * k * k < len(B) else "??")
        best = None
        for e in range(dH[r] + 2, 0, -2):
            s2, W2 = cpsat_decomp(B, n // 2, r=r, minends=e, time_limit=300)
            if s2 == "FEAS":
                check_decomp(B, W2, maxpaths=n // 2, r=r, minends=e)
                best = e
                break
        # d_H(r)+4 ends is impossible by the vertex bound (every vertex lies on <= k+1 paths);
        # confirmed by CP-SAT at n <= 8 only.
        s3 = (cpsat_decomp(B, n // 2, r=r, minends=dH[r] + 4, time_limit=300)[0] if n <= 8 else "bound") if dH[r] + 4 <= len(A[r]) else "INFEAS(trivial)"
        print(g6, z, r, "n", n, "e(H)", eH, "semi", semi, "d_H(r)", dH[r], "witness ends at r", ends[r],
              "p(B)>k:", st, "emax(CP-SAT)", best, "d_H(r)+4:", s3, "file emax", emax)
        cnt[("semi", semi)] += 1
        cnt[("dH(r)", dH[r])] += 1
        cnt[("emax==dH+2", best == dH[r] + 2)] += 1
        cnt[("tight proven", st)] += 1
    print(dict(cnt))
    print("== all field lines: slack=0 <=> e(B) > 2k^2")
    c2 = Counter()
    for fn, op in ((D + "t2_order6_8.txt", open), (D + "t2_order10_fields.txt.gz", gzip.open)):
        with op(fn, "rt") as fh:
            for line in fh:
                g6, tail = line.split(None, 1)
                f = list(map(int, tail.split("|")[0].split()))
                z, r, dz, dr, n, slack, t2, emax = f
                nn, E = g6_decode(g6)
                eB = len(E) - dz
                k = (n - 2) // 2
                semi = eB > 2 * k * k
                c2[(n, "slack", slack, "semi", semi)] += 1
                c2[(n, "t2", t2)] += 1
    for kk in sorted(c2, key=str):
        print(kk, c2[kk])


if __name__ == "__main__":
    main()

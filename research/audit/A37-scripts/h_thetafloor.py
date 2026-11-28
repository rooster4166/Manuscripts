"""h_thetafloor.py (audit A37): the floor base at the fat theta (manuscript Section 5: 'absent at the
fat theta, where the floor holds').  Own exhaustive code: every w in N(z) - r, every forest
T'-join Phi of B (T' = N(z) - {r, w}), every rooting with w a root of its component (if present),
every Lovasz decomposition of B - Phi (w its only even vertex), conditions (i), (ii).  Also: the
floor p(B) <= k by CP-SAT (witness checked).
usage: python3 h_thetafloor.py G6 z r
"""
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from a37lib import adjacency, check_decomp, cpsat_decomp, delete_vertex, g6_decode
from d_theta import forest_tjoins, is_base, rootings
from h_bases8 import lovasz_gen


def main():
    g6, z, r = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    n, E = g6_decode(g6)
    A = adjacency(n, E)
    B = delete_vertex(E, z)
    k = (n - 2) // 2
    s, W = cpsat_decomp(B, k)
    if s == "FEAS":
        check_decomp(B, W, maxpaths=k)
    print("floor p(B) <= k:", s, W)
    tried = bases = 0
    for w in sorted(A[z]):
        if w == r:
            continue
        Tp = [v for v in A[z] if v not in (r, w)]
        for F in forest_tjoins(B, Tp):
            G = B - set(F)
            AG = adjacency(n, G)
            b = [len(AG[v]) % 2 if v != z else 0 for v in range(n)]
            assert b[w] == 0 and all(b[v] == 1 for v in range(n) if v not in (z, w))
            Ds = list(lovasz_gen(n, G, b))
            for roots, par, order in rootings(F):
                if w in par:
                    continue
                tried += 1
                bases += sum(1 for D in Ds if is_base(D, par))
    print("rootings tried", tried, "floor bases found", bases)


if __name__ == "__main__":
    main()

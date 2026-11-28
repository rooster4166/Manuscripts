"""ex_t1theta.py -- audit A37b, item 1 (Example ex:t1theta): exhaustive all-odd base search.

For each instance (J, z, r): every forest N(z)-join, every admissible rooting (r a root or a
child with c(r) >= 2), each decided exactly by ./obase.  Also (T1) itself is decided by CP-SAT
(a37lib.cpsat_decomp) and the witness checked.
usage: python3 ex_t1theta.py G6 [z]      (z defaults to the unique even vertex)
"""
import sys

from oddbase_lib import (Obase, decide_base, is_forest, lift_and_check, rootings, t1_instances,
                         tjoins)
from a37lib import cpsat_decomp, check_decomp, g6_decode


def main():
    g6 = sys.argv[1]
    n, E = g6_decode(g6)
    z, rs = t1_instances(n, E)
    assert z is not None, "not a (T1) graph (3-connected, one even vertex)"
    if len(sys.argv) > 2:
        assert int(sys.argv[2]) == z
    Bverts = [v for v in range(n) if v != z]
    Bedges = [tuple(sorted(e)) for e in E if z not in e]
    T = set(rs)
    ob = Obase()
    alls = tjoins(Bverts, Bedges, T)
    forests = [phi for phi in alls if is_forest(phi)]
    print(f"{g6} z={z} N(z)={rs}: T-joins {len(alls)}, forest T-joins {len(forests)}")
    for r in rs:
        nroot = nchild = broot = bchild = 0
        wit = None
        for phi in forests:
            for par, order in rootings(phi, r):
                child = r in par
                if child:
                    nchild += 1
                else:
                    nroot += 1
                H, D0 = decide_base(ob, n, Bverts, Bedges, phi, par)
                if D0 is not None:
                    e = lift_and_check(E, z, r, n, H, par, order, D0)
                    if child:
                        bchild += 1
                    else:
                        broot += 1
                    if wit is None:
                        wit = (sorted(phi), par, D0, e)
        st, P = cpsat_decomp({e for e in E if z not in e}, (n - 1) // 2, r=r, minends=2,
                             time_limit=120)
        if st == "FEAS":
            check_decomp({e for e in E if z not in e}, P, maxpaths=(n - 1) // 2, r=r, minends=2)
        print(f"  r={r}: rootings with r a root {nroot} (bases {broot}), r a child {nchild} "
              f"(bases {bchild}); (T1) by CP-SAT: {st}{' witness ' + str(P) if P else ''}")
        if wit:
            print("    first base:", wit)


if __name__ == "__main__":
    main()

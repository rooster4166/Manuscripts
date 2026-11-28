"""tb2_pm.py: the (T2) matching (triangle) base, per perfect matching (test2 session).

For every instance (J, z, r) and every perfect matching M0 of J[N(z)] (edges of J), with r matched
to a0: M = J - {zv : v in N(z) - r} - M0 (no even vertex; z a leaf at r).  The matching base asks
for a Lovasz decomposition of M with
    r not in V(Q(a0))   and, for every other pair ab of M0,   a not in Q(b) or b not in Q(a).
Each condition alone holds in some Lovasz decomposition by L1 (lovasz_avoid_nonadj; M has no
even vertex and the pair is non-adjacent in M).  This script decides, exactly (route_ext C, no
budget), whether they hold together, for every matching, and lifts and verifies every base found.
Output per (instance, matching):  g6 z r dz M0 status   with status BASE or NOBASE.
Summary on stderr.
usage: python3 tb2_pm.py ORACLE < instances
"""
import sys
from collections import Counter

import networkx as nx

from tb2 import Oracle, base_graph, check_base, lift, parse_paths, perfect_matchings, \
    query_line, rootings, verify_test2


def main():
    oracle = Oracle(sys.argv[1])
    stats = Counter()
    for line in sys.stdin:
        if not line.strip():
            continue
        g6, tail = line.split(None, 1)
        f = tail.split("|")[0].split()
        z, r = int(f[0]), int(f[1])
        J = nx.from_graph6_bytes(g6.encode())
        n = J.number_of_nodes()
        T = sorted(J[z])
        pms = list(perfect_matchings(T, J))
        stats["instances"] += 1
        if not pms:
            stats["no matching data"] += 1
            continue
        stats["with matching data"] += 1
        inst_ok = False
        for pm in pms:
            M = base_graph(J, z, r, pm)
            ok = False
            for par, order in rootings(pm, r, 10 ** 6):
                o = oracle.query(query_line(M, n, par, 0, 7))
                assert o[0] in "01", o
                if o.startswith("1"):
                    D0 = parse_paths(o)
                    check_base(M, n, par, D0)
                    verify_test2(J, z, r, lift(J, z, r, par, order, D0))
                    ok = True
                    break
            stats["matchings"] += 1
            stats["matchings with base" if ok else "matchings without base"] += 1
            inst_ok |= ok
            print(g6, z, r, J.degree(z), ";".join(f"{a}-{b}" for a, b in pm),
                  "BASE" if ok else "NOBASE", flush=True)
        stats["instances with a matching base" if inst_ok else "instances with data, no base"] += 1
    print("SUMMARY", dict(stats), file=sys.stderr)


if __name__ == "__main__":
    main()

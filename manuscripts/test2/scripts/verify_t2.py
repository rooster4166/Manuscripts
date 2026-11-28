"""verify_t2.py: independent check of the witness lines printed by t2.c.

Each line 'g6 z r dz dr n slack t2 emax | v0 v1 ... | ... |' with t2 = 1 is checked:
  * z, r are the only even-degree vertices of J and are adjacent; n = |V(J)|;
  * every listed sequence is a path of B = J - z (consecutive vertices adjacent, no repeated
    vertex, at least one edge), and the paths partition E(B);
  * there are at most n/2 paths and at least three of them end at r.
If the line carries a slack witness (t2.c -s: the token S, then paths), it is checked as a
decomposition of B into at most n/2 - 1 paths, and slack must be 1; with --require-slack, every
line with slack = 1 must carry one.
Lines with t2 != 1 are counted and printed.  Exits with status 1 on the first error.
usage: python3 verify_t2.py [--require-slack] < t2_output
"""
import sys

import networkx as nx


REQUIRE_SLACK = False
NSLACK = [0]


def check_partition(B, paths, line):
    used = set()
    ends = {v: 0 for v in B}
    for P in paths:
        assert len(P) >= 2 and len(set(P)) == len(P), (line, P)
        for x, y in zip(P, P[1:]):
            e = frozenset((x, y))
            assert B.has_edge(x, y), (line, P, x, y)
            assert e not in used, (line, P, x, y)
            used.add(e)
        ends[P[0]] += 1
        ends[P[-1]] += 1
    assert len(used) == B.number_of_edges(), line
    return ends


def check(line):
    g6, tail = line.split(None, 1)  # graph6 may contain '|'
    head, *rest = tail.split("|")
    f = list(map(int, head.split()))
    z, r, dz, dr, n, slack, t2, emax = f
    J = nx.from_graph6_bytes(g6.encode())
    assert J.number_of_nodes() == n
    ev = sorted(v for v in J if J.degree(v) % 2 == 0)
    assert ev == sorted((z, r)) and J.has_edge(z, r), line
    assert J.degree(z) == dz and J.degree(r) == dr
    segs = [x.strip() for x in rest]
    swit = None
    if "S" in segs:
        i = segs.index("S")
        segs, swit = segs[:i], segs[i + 1:]
    B = J.copy()
    B.remove_node(z)
    if swit is not None:
        assert slack == 1, line
        sp = [list(map(int, x.split())) for x in swit if x]
        check_partition(B, sp, line)
        assert len(sp) <= n // 2 - 1, line
        NSLACK[0] += 1
    elif REQUIRE_SLACK:
        assert slack != 1, ("slack without witness", line)
    if t2 != 1:
        return t2
    paths = [list(map(int, x.split())) for x in segs if x]
    ends = check_partition(B, paths, line)
    assert len(paths) <= n // 2, line
    assert ends[r] >= 3, line
    return 1


def main():
    global REQUIRE_SLACK
    REQUIRE_SLACK = "--require-slack" in sys.argv
    cnt = {}
    for line in sys.stdin:
        line = line.rstrip("\n")
        if not line.strip():
            continue
        res = check(line)
        cnt[res] = cnt.get(res, 0) + 1
        if res != 1:
            print("NOT VERIFIED (t2 =", res, "):", line)
    print("verified witnesses:", cnt.get(1, 0), " slack witnesses:", NSLACK[0],
          " other:", {k: v for k, v in cnt.items() if k != 1})


if __name__ == "__main__":
    main()

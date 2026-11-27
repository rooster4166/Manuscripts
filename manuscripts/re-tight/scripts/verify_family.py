"""verify_family.py [-z]: independent check of the witnesses printed by ret.c (stdin).

For every YES line 'g6 r YES q | att:v0,...,vl ; ... | x-y ... | ...' it checks:
  * d(r) = n - 2; G = B - r;
  * there is exactly one member per x in N(r), with attachment x = v0;
  * each nontrivial member is a path of G (distinct vertices, consecutive vertices adjacent);
  * the nontrivial members partition E(G);
  * the printed pairs are vertex-disjoint members, each member used at most once, and there are
    at least k - 2 pairs (with -z: exactly k - 1);
  * the reassembled family is a decomposition of B into at most k paths (k - 1 with -z) with
    at least two ends at r (with -z: every path through r), checked from scratch.
Prints a summary; exits with status 1 on any failure.
"""
import sys

import networkx as nx


def check(line, zmode):
    g6, rest = line.split(None, 1)  # graph6 may contain '|'
    head, fam, pairs, _ = rest.split("|", 3)
    r, st, q = head.split()
    r = int(r)
    B = nx.from_graph6_bytes(g6.encode())
    n = B.number_of_nodes()
    k = n // 2
    assert B.degree(r) == n - 2, "degree"
    N = set(B[r])
    G = B.copy()
    G.remove_node(r)
    mem = {}
    for tok in fam.split(";"):
        tok = tok.strip()
        if not tok:
            continue
        a, seq = tok.split(":")
        a = int(a)
        seq = [int(x) for x in seq.split(",")]
        assert seq[0] == a, "attachment is v0"
        assert a in N and a not in mem, "attachment in N(r), once"
        mem[a] = seq
    assert set(mem) == N, "one member per neighbour"
    used = set()
    for a, seq in mem.items():
        assert len(set(seq)) == len(seq), "path vertices distinct"
        for u, v in zip(seq, seq[1:]):
            assert G.has_edge(u, v), "edge of G"
            e = frozenset((u, v))
            assert e not in used, "edge used once"
            used.add(e)
    assert len(used) == G.number_of_edges(), "all edges of G covered"
    pl = [tuple(int(x) for x in t.split("-")) for t in pairs.split()]
    seen = set()
    for x, y in pl:
        assert x in mem and y in mem and x not in seen and y not in seen and x != y
        seen |= {x, y}
        assert not (set(mem[x]) & set(mem[y])), "pair disjoint"
    if zmode:
        assert len(pl) == k - 1
    else:
        assert len(pl) >= k - 2
    # reassemble
    paths = []
    for x, y in pl:
        paths.append(list(reversed(mem[x])) + [r] + mem[y])
    single = [x for x in mem if x not in seen]
    if not zmode:
        # if k - 1 pairs were printed, split one of them at r
        if len(pl) == k - 1:
            P = paths.pop()
            i = P.index(r)
            paths += [P[: i + 1], P[i:]]
        for x in single:
            paths.append(list(reversed(mem[x])) + [r])
    else:
        assert not single
    # decomposition check from scratch
    eds = set()
    ends_r = 0
    for P in paths:
        assert len(P) >= 2 and len(set(P)) == len(P)
        for u, v in zip(P, P[1:]):
            assert B.has_edge(u, v)
            e = frozenset((u, v))
            assert e not in eds
            eds.add(e)
        ends_r += (P[0] == r) + (P[-1] == r)
    assert len(eds) == B.number_of_edges()
    if zmode:
        assert len(paths) == k - 1 and ends_r == 0
    else:
        assert len(paths) <= k and ends_r >= 2
    return int(q)


def main():
    zmode = "-z" in sys.argv
    ok = bad = other = 0
    for line in sys.stdin:
        f = line.split()
        if len(f) < 3:
            continue
        if f[2] != "YES":
            other += 1
            continue
        try:
            check(line, zmode)
            ok += 1
        except AssertionError as e:
            bad += 1
            print("FAIL", line.strip()[:120], e)
    print("verified %d witnesses, %d failures, %d non-YES lines" % (ok, bad, other))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()

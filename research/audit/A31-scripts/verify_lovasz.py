"""verify_lovasz.py FILE...: check that every YES witness of ret.c -L is a *Lovasz* family, and a
valid RE family (own code; verify_family.py checks only the latter).

Lovasz family: k - 1 nontrivial members, every x in N(r) is an end of exactly one of them, s is
an end of none, and the trivial members are exactly the non-attachment ends.  Plus: members are
paths of G = B - r partitioning E(G), the printed pairs are disjoint members, >= k - 2 pairs.
"""
import sys
from collections import Counter

sys.path.insert(0, __import__("os").path.dirname(__file__))
from g6 import parse_g6  # noqa: E402


def check(line):
    g6, rest = line.split(None, 1)
    head, fam, pairs, _ = rest.split("|", 3)
    r = int(head.split()[0])
    n, adj = parse_g6(g6)
    k = n // 2
    assert len(adj[r]) == n - 2
    N = set(adj[r])
    s = [v for v in range(n) if v != r and v not in N][0]
    mem = {}
    for tok in fam.split(";"):
        tok = tok.strip()
        if not tok:
            continue
        a, seq = tok.split(":")
        mem[int(a)] = [int(x) for x in seq.split(",")]
    assert set(mem) == N
    used = set()
    endc = Counter()
    nontriv = 0
    for a, P in mem.items():
        assert P[0] == a and len(set(P)) == len(P) and r not in P
        for u, v in zip(P, P[1:]):
            assert v in adj[u]
            e = frozenset((u, v))
            assert e not in used
            used.add(e)
        if len(P) > 1:
            nontriv += 1
            endc[P[0]] += 1
            endc[P[-1]] += 1
    mG = sum(len(adj[v] - {r}) for v in range(n) if v != r) // 2
    assert len(used) == mG
    assert nontriv == k - 1, "k-1 nontrivial members"
    assert all(endc[x] == 1 for x in N), "each x in N an end exactly once"
    assert endc[s] == 0, "s not an end"
    far = {mem[a][-1] for a in mem if len(mem[a]) > 1}
    triv = {a for a in mem if len(mem[a]) == 1}
    assert far == triv, "trivial members = far ends"
    pl = [tuple(int(x) for x in t.split("-")) for t in pairs.split()]
    seen = set()
    for x, y in pl:
        assert x not in seen and y not in seen and x != y
        seen |= {x, y}
        assert not set(mem[x]) & set(mem[y])
    assert len(pl) >= k - 2


def main():
    c = Counter()
    for fn in sys.argv[1:]:
        for line in open(fn):
            f = line.split()
            if len(f) < 3 or f[2] != "YES":
                c[(fn.split("/")[-1], "non-YES")] += 1
                continue
            try:
                check(line)
                c[(fn.split("/")[-1], "Lovasz OK")] += 1
            except AssertionError as e:
                c[(fn.split("/")[-1], "FAIL")] += 1
                print("FAIL", line[:100], e)
    for kk in sorted(c):
        print(kk, c[kk])


if __name__ == "__main__":
    main()

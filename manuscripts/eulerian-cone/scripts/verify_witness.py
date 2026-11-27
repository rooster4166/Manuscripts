"""verify_witness.py: independent check of the witness lines printed by re.c.

Each line 'g6 r p k STATUS | v0 v1 ... | ... |' with STATUS OK is checked:
  * every listed sequence is a path of B (consecutive vertices adjacent, no repeated vertex,
    at least one edge);
  * the paths partition E(B) (every edge exactly once);
  * the number of paths equals p (and p <= k);
  * r is an end of at least one path (root field r >= 0), and when every degree of B is even,
    of at least two.
Lines with root -1 (unrooted mode) are checked without the end condition.
Prints a summary; exits with status 1 on the first error.
usage: python3 verify_witness.py < re_output
"""
import sys

import networkx as nx


def check(line):
    g6, tail = line.split(None, 1)  # graph6 may itself contain '|'
    head, *rest = tail.split("|")
    f = head.split()
    r, p, k, st = int(f[0]), int(f[1]), int(f[2]), f[3]
    if st != "OK" and st != "OVER":
        return st
    B = nx.from_graph6_bytes(g6.encode())
    paths = [list(map(int, s.split())) for s in rest if s.strip()]
    assert len(paths) == p, (line, len(paths), p)
    if st == "OK":
        assert p <= k, line
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
    if r >= 0:
        assert ends[r] >= 1, line
        if all(d % 2 == 0 for _, d in B.degree()):
            assert ends[r] >= 2, line
    return "VERIFIED"


def main():
    counts = {}
    for line in sys.stdin:
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        res = check(line)
        counts[res] = counts.get(res, 0) + 1
    print(counts)


if __name__ == "__main__":
    main()

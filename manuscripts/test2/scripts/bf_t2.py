"""bf_t2.py: brute force for (T2), independent of t2.c.

For each line of t2.c output (only the fields g6 z r are read), list every path of B = J - z
explicitly, enumerate all exact covers of E(B) by listed paths with no pruning beyond the size
cap n/2, and report
  slack = [some cover has <= n/2 - 1 paths],
  t2    = [some cover has <= n/2 paths and >= 3 ends at r],
  emax  = the largest number of ends at r over covers with <= n/2 paths.
Compares with the t2.c fields and prints mismatches.  Small graphs only.
usage: python3 bf_t2.py < t2_output
"""
import sys

import networkx as nx


def all_paths(B):
    seen = set()
    out = []

    def grow(seq, vs):
        if len(seq) >= 2:
            es = frozenset(frozenset(e) for e in zip(seq, seq[1:]))
            key = (es, frozenset((seq[0], seq[-1])))
            if key not in seen:
                seen.add(key)
                out.append((es, (seq[0], seq[-1])))
        for y in B[seq[-1]]:
            if y not in vs:
                seq.append(y)
                vs.add(y)
                grow(seq, vs)
                vs.remove(y)
                seq.pop()

    for v in B:
        grow([v], {v})
    return out


def analyse(J, z, r):
    B = J.copy()
    B.remove_node(z)
    n = J.number_of_nodes()
    cap = n // 2
    E = sorted(frozenset(e) for e in B.edges())
    order = {e: i for i, e in enumerate(sorted(E, key=lambda e: tuple(sorted(e))))}
    by_edge = {e: [] for e in E}
    for es, ends in all_paths(B):
        for e in es:
            by_edge[e].append((es, ends))
    best = {"slack": False, "emax": -1}

    def rec(unc, cnt, er):
        if not unc:
            if cnt <= cap - 1:
                best["slack"] = True
            if er > best["emax"]:
                best["emax"] = er
            return
        if cnt >= cap:
            return
        e = min(unc, key=lambda x: order[x])
        for es, ends in by_edge[e]:
            if es <= unc:
                rec(unc - es, cnt + 1, er + (ends[0] == r) + (ends[1] == r))

    rec(frozenset(E), 0, 0)
    return best["slack"], best["emax"] >= 3, best["emax"]


def main():
    bad = tot = 0
    for line in sys.stdin:
        if not line.strip():
            continue
        g6, tail = line.split(None, 1)
        f = list(map(int, tail.split("|")[0].split()))
        z, r, slack, t2, emax = f[0], f[1], f[5], f[6], f[7]
        J = nx.from_graph6_bytes(g6.encode())
        s2, t22, e2 = analyse(J, z, r)
        tot += 1
        if (int(s2), int(t22)) != (slack, t2) or (emax != -1 and e2 != emax):
            bad += 1
            print("MISMATCH", line.strip()[:60], "bf:", int(s2), int(t22), e2)
    print("bf_t2: instances", tot, "mismatches", bad)


if __name__ == "__main__":
    main()

"""bf.py: brute-force rooted path number, independent of re.c.

All paths of B are listed explicitly (as edge sets).  A decomposition is then an exact cover of
E(B) by listed paths; it is searched by plain recursion on the lowest uncovered edge, with no
lower bound and no memo.  p_r(B) is the least size of a cover in which some path has r as an end
(r ranges over all vertices).  Feasible for small graphs only (about 12 edges).

usage: python3 bf.py < g6_lines     prints 'g6 p_0 p_1 ... p_{n-1} | p' per graph
"""
import sys

import networkx as nx


def all_paths(B):
    """Every path of B with at least one edge, once (as a frozenset of edges, with its ends)."""
    seen = {}

    def grow(seq, vs):
        if len(seq) >= 2:
            es = frozenset(frozenset(e) for e in zip(seq, seq[1:]))
            key = (es, frozenset((seq[0], seq[-1])))
            seen[key] = 1
        for y in B[seq[-1]]:
            if y not in vs:
                seq.append(y)
                vs.add(y)
                grow(seq, vs)
                vs.remove(y)
                seq.pop()

    for v in B:
        grow([v], {v})
    return [(es, ends) for (es, ends) in seen]


def best(B, need_root):
    E = [frozenset(e) for e in B.edges()]
    paths = all_paths(B)
    by_edge = {e: [] for e in E}
    for es, ends in paths:
        for e in es:
            by_edge[e].append((es, ends))
    order = {e: i for i, e in enumerate(E)}
    n = B.number_of_nodes()
    best_val = {r: None for r in B} if need_root else None
    # enumerate all exact covers, recording (size, set of end vertices)
    results = []

    def rec(uncovered, cnt, endset):
        if not uncovered:
            results.append((cnt, frozenset(endset)))
            return
        e = min(uncovered, key=lambda x: order[x])
        for es, ends in by_edge[e]:
            if es <= uncovered:
                rec(uncovered - es, cnt + 1, endset | ends)

    rec(frozenset(E), 0, frozenset())
    p = min(c for c, _ in results)
    pr = []
    for r in sorted(B):
        cands = [c for c, s in results if r in s]
        pr.append(min(cands) if cands else -1)
    return pr, p


def main():
    for line in sys.stdin:
        g6 = line.strip()
        if not g6:
            continue
        B = nx.from_graph6_bytes(g6.encode())
        pr, p = best(B, True)
        print(g6, " ".join(map(str, pr)), "|", p)
        sys.stdout.flush()


if __name__ == "__main__":
    main()

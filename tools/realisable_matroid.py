"""Is the family F of realisable even-vertex sets the spanning-set family of a matroid?

S subset of E (even vertices) is realisable if some decomposition has 2 ends at
each vertex of S, 0 on E - S and exactly 1 at each odd vertex.  F is an up-set
(split a path at an unexposed even vertex).  F is the spanning-set family of a
matroid iff its minimal members all have one size and satisfy basis exchange.
"""
import itertools
import sys
import networkx as nx
from faithful_descent import make_oracle


def analyse(G):
    E, O, real = make_oracle(G)
    e = len(E)
    if e == 0:
        return None
    F = set()
    for size in range(e + 1):
        for S in itertools.combinations(E, size):
            S = frozenset(S)
            # up-set shortcut
            if any((S - {v}) in F for v in S):
                F.add(S)
            elif real(S):
                F.add(S)
    minimal = [S for S in F if not any((S - {v}) in F for v in S)]
    sizes = sorted(set(len(S) for S in minimal))
    exch = True
    if len(sizes) == 1:
        B = set(minimal)
        for X in B:
            for Y in B:
                for x in X - Y:
                    if not any(((X - {x}) | {y}) in B for y in Y - X):
                        exch = False
    loops = [v for v in E if not any(v in S for S in minimal)]
    return e, sizes, exch and len(sizes) == 1, loops


if __name__ == "__main__":
    from collections import Counter
    stats = Counter()
    for line in open(sys.argv[1]):
        G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(line.strip().encode()))
        res = analyse(G)
        if res is None:
            continue
        e, sizes, is_matroid, loops = res
        crit = G.number_of_nodes() % 2 == 0 and sizes[0] == e // 2
        stats[("matroid" if is_matroid else "NOT matroid", "critical" if crit else "noncritical")] += 1
        if not is_matroid:
            print("NONMATROID", line.strip(), "e=", e, "minimal sizes", sizes)
        if loops and crit:
            print("LOOP (rooted fail?)", line.strip(), loops)
    print(dict(stats))

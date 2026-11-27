"""near_regular.py N COUNT SEED [C]: random Eulerian graphs B of order N in which vertex 0 has degree
N - 2 and every other vertex has degree N - 1 - C (C odd, default 3), i.e. the complement is a
random simple graph with degree 1 at vertex 0 and C elsewhere.  Only the root 0 has degree N - 2, so
marked-reduction Thm 170 does not apply once N/2 - 1 > 1.  Prints graph6 (root 0) for the
2-connected ones.
"""
import random
import sys

import networkx as nx


def main():
    n, count, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    c = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    rng = random.Random(seed)
    seq = [1] + [c] * (n - 1)
    if sum(seq) % 2:
        raise SystemExit("degree sum odd")
    out = 0
    seen = set()
    while out < count:
        try:
            H = nx.random_degree_sequence_graph(seq, seed=rng.randrange(1 << 30), tries=50)
        except nx.NetworkXUnfeasible:
            continue
        B = nx.complement(H)
        if not all(d % 2 == 0 for _, d in B.degree()) or B.degree(0) != n - 2:
            continue
        if not nx.is_biconnected(B):
            continue
        g6 = nx.to_graph6_bytes(B, header=False).decode().strip()
        if g6 in seen:
            continue
        seen.add(g6)
        print(g6)
        out += 1


if __name__ == "__main__":
    main()

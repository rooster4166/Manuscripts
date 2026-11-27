"""Cross-check of the oracle l1s (mode ed) against the independent brute force brute.py.
For every connected graph of order n read from stdin with at most one vertex of positive even
degree, every odd c and every subset A of V - {c} (all subsets, not only L1* instances), compare
"some Lovász decomposition has Q_c disjoint from A".
usage: nauty-geng -cq n | python3 xcheck_brute.py
"""
import sys, itertools, subprocess, os
import networkx as nx
from brute import lovasz_decomps
HERE = os.path.dirname(os.path.abspath(__file__))
p = subprocess.Popen([os.path.join(HERE, "l1s"), "ed", "0"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
tot = bad = 0
for line in sys.stdin:
    G = nx.from_graph6_bytes(line.strip().encode())
    if len([v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]) > 1:
        continue
    decs = list(lovasz_decomps(G))
    E = list(G.edges())
    for c in G:
        if G.degree(c) % 2 == 0:
            continue
        supports = [set(q) for P in decs for q in P if q[0] == c or q[-1] == c]
        others = [v for v in G if v != c]
        for k in range(len(others) + 1):
            for S in itertools.combinations(others, k):
                A = set(S)
                br = any(not (s & A) for s in supports)
                p.stdin.write(f"{G.number_of_nodes()} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + f" {c} {sum(1 << a for a in A)}\n")
                p.stdin.flush()
                r = int(p.stdout.readline())
                tot += 1
                if r != int(br):
                    bad += 1
                    print("MISMATCH", line.strip(), c, sorted(A), r, br)
print(f"SUMMARY xcheck queries={tot} mismatches={bad}")

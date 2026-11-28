"""xcheck_fl.py: independent check of fl.c on small orders (nodata session).

Re-enumerates, with networkx, the constraint sets of the families kp (2-chain + pair), cp (3-chain
+ pair), s (star) and l (claw) on every connected graph with no even vertex in the input, and
decides each with tools/route_ext.c query C (masks {v, p(v)}).  Prints (family, answer) counts, to
compare with the SUMMARY lines of fl.c (sets = total, failures = answers 0).
usage: python3 xcheck_fl.py ROUTE_EXT < graph6
"""
import itertools
import subprocess
import sys
from collections import Counter
import networkx as nx


def main():
    qs, meta = [], []
    for g in sys.stdin:
        g = g.strip()
        if not g:
            continue
        G = nx.from_graph6_bytes(g.encode())
        if not nx.is_connected(G) or any(d % 2 == 0 for _, d in G.degree()):
            continue
        n = G.number_of_nodes()
        E = sorted(G.edges())
        na = lambda u, v: u != v and not G.has_edge(u, v)
        head = "C %d %d %s %s " % (n, len(E), " ".join(f"{u} {v}" for u, v in E), " ".join(["1"] * n))

        def add(fam, par):
            crv = [1 << v for v in range(n)]
            for v, p in par:
                crv[v] |= 1 << p
            qs.append(head + " ".join(map(str, crv)))
            meta.append(fam)

        for a, x, b in itertools.permutations(range(n), 3):
            if na(a, x) and na(x, b):
                for c, d in itertools.permutations([v for v in range(n) if v not in (a, x, b)], 2):
                    if na(c, d):
                        add("kp", [(x, a), (b, x), (c, d)])
        for a, x, y, b in itertools.permutations(range(n), 4):
            if na(a, x) and na(x, y) and na(y, b):
                for c, d in itertools.permutations([v for v in range(n) if v not in (a, x, y, b)], 2):
                    if na(c, d):
                        add("cp", [(x, a), (y, x), (b, y), (c, d)])
        for u in range(n):
            for x, y in itertools.combinations(range(n), 2):
                if u not in (x, y) and na(u, x) and na(u, y):
                    add("s", [(x, u), (y, u)])
        for a, v in itertools.permutations(range(n), 2):
            for b, c in itertools.combinations([w for w in range(n) if w not in (a, v)], 2):
                if na(a, v) and na(v, b) and na(v, c):
                    add("l", [(v, a), (b, v), (c, v)])
    out = subprocess.run([sys.argv[1]], input="\n".join(qs) + "\n", capture_output=True, text=True).stdout.split()
    assert len(out) == len(qs)
    print("XCHECK_FL", sorted(Counter(zip(meta, out)).items()))


if __name__ == "__main__":
    main()

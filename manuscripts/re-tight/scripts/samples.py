"""samples.py OUTDIR: regenerate the order-12 to 16 sample inputs of re-tight Section 5.3.

Writes, into OUTDIR:
  rand12_n2.g6     the graphs of eulerian-cone rand_12.g6 with a vertex of degree 10 (in file order);
  mid12_sample.g6  400 graphs of the dense order-12 family (dense12_2c + dense12_m45_2c, m >= 45)
                   with 1 to 4 vertices of degree 10, chosen by random.seed(12) and a shuffle;
  nr12.g6, nr14.g6, nr16.g6
                   near-regular graphs (near_regular.py with N, COUNT, SEED = 12 20 1, 14 10 2,
                   16 10 3): only vertex 0 has degree N - 2, all others N - 4;
  mixed16.g6       order 16, u = 2..6 vertices of complement degree 1 (B-degree 14, vertex 0 among
                   them), the others complement degree 3 (B-degree 12); six 2-connected graphs per u,
                   from random.Random(5);
  m16_u4.g6, m16_u6.g6
                   lines 13 and 25 of mixed16.g6 (a graph with u = 4 and one with u = 6).
Graphs come from networkx.random_degree_sequence_graph, so exact reproduction needs a networkx with
the same generator (the shipped files were made with networkx 3.7).
"""
import gzip
import os
import random
import subprocess
import sys

import networkx as nx

E = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "eulerian-cone", "data")


def g6(B):
    return nx.to_graph6_bytes(B, header=False).decode().strip()


def main():
    out = sys.argv[1]
    # random order 12
    rs = []
    for line in open(os.path.join(E, "rand_12.g6")):
        B = nx.from_graph6_bytes(line.strip().encode())
        if any(d == 10 for _, d in B.degree()):
            rs.append(line.strip())
    open(os.path.join(out, "rand12_n2.g6"), "w").write("\n".join(rs) + "\n")
    # dense order 12, 1..4 vertices of degree 10
    random.seed(12)
    mid = []
    for fn in ("dense12_2c.g6.gz", "dense12_m45_2c.g6.gz"):
        for line in gzip.open(os.path.join(E, fn), "rt"):
            g = line.strip()
            B = nx.from_graph6_bytes(g.encode())
            u = sum(1 for _, d in B.degree() if d == 10)
            if 1 <= u < 5:
                mid.append(g)
    random.shuffle(mid)
    open(os.path.join(out, "mid12_sample.g6"), "w").write("\n".join(mid[:400]) + "\n")
    # near-regular
    here = os.path.dirname(os.path.abspath(__file__))
    for n, cnt, seed in ((12, 20, 1), (14, 10, 2), (16, 10, 3)):
        res = subprocess.run([sys.executable, os.path.join(here, "near_regular.py"), str(n), str(cnt),
                              str(seed)], capture_output=True, text=True, check=True).stdout
        open(os.path.join(out, "nr%d.g6" % n), "w").write(res)
    # mixed order 16
    rng = random.Random(5)
    lines = []
    for u in (2, 3, 4, 5, 6):
        made = 0
        while made < 6:
            seq = [1] * u + [3] * (16 - u)
            if sum(seq) % 2:
                seq[-1] = 5
            try:
                H = nx.random_degree_sequence_graph(seq, seed=rng.randrange(1 << 30), tries=50)
            except Exception:
                continue
            B = nx.complement(H)
            if not all(d % 2 == 0 for _, d in B.degree()) or not nx.is_biconnected(B):
                continue
            lines.append(g6(B))
            made += 1
    open(os.path.join(out, "mixed16.g6"), "w").write("\n".join(lines) + "\n")
    open(os.path.join(out, "m16_u4.g6"), "w").write(lines[12] + "\n")
    open(os.path.join(out, "m16_u6.g6"), "w").write(lines[24] + "\n")


if __name__ == "__main__":
    main()

# every root certified by Theorem A or B must have ALLD=1 in drm -A -m 0 (every Lovasz D0 works)
import sys, networkx as nx
src = open('thm_cov.py').read()
exec(src.split("C = Counter()")[0])
exec("\n".join(src.split("# ---- extended")[1].split("C2 = Counter()")[0].split("\n")[1:]))
alld = {}
for line in open('../data/drmA9_m0.out'):
    f = line.split(); alld[(f[0], int(f[1]))] = f[3]
bad = 0; nA = nB = 0
for line in open(sys.argv[1]):
    g6 = line.split()[0]
    J = nx.from_graph6_bytes(g6.encode()); n = J.number_of_nodes(); k = (n - 1) // 2
    z = [v for v in J if J.degree(v) % 2 == 0][0]; Z = set(J[z]); B = J.copy(); B.remove_node(z)
    for r in sorted(Z):
        if J.degree(r) != n - 2: continue
        s = [v for v in B if v != r and not B.has_edge(r, v)][0]
        a = thmA(B, r, s, k) is True; b = thmB2(B, r, s, k, Z) is True
        nA += a; nB += b
        if (a or b) and alld[(g6, r)] != 'ALLD=1': bad += 1; print('MISMATCH', g6, r, a, b)
print('A', nA, 'B', nB, 'mismatches', bad)

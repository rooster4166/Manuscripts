"""filt.py: J with exactly one even vertex z, d(z) = D, kappa(J) >= 3 (graph6 of J per line).
usage: filt.py D < g6 > g6"""
import sys
import networkx as nx
D = int(sys.argv[1])
for line in sys.stdin:
    s = line.split()[0] if line.strip() else ''
    if not s: continue
    J = nx.from_graph6_bytes(s.encode())
    ev = [v for v in J if J.degree(v) % 2 == 0]
    if len(ev) != 1 or J.degree(ev[0]) != D: continue
    if nx.node_connectivity(J) < 3: continue
    print(s)

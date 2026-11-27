"""Move certificates for the EE instances (K, z, u) -> (K - uz, z, {u}).  (exploratory)"""
import sys, collections
import networkx as nx
import cert
cert.MOVES = set(sys.argv[1].split(",")) if len(sys.argv) > 1 else {"M1", "M2", "M2p", "M3", "M7", "M8", "M9", "M13", "B"}
C = collections.Counter(); ex = []
for line in sys.stdin:
    line = line.strip()
    K = nx.from_graph6_bytes(line.encode())
    ev = [v for v in K if K.degree(v) > 0 and K.degree(v) % 2 == 0]
    if len(ev) != 1: continue
    z = ev[0]
    for u in sorted(K[z]):
        if K.degree(u) < 3: continue
        T = len(set(K[u]) & set(K[z]))
        G = K.copy(); G.remove_edge(u, z)
        ok = cert.cert(G, z, frozenset({u}))
        C[(min(T, 3), ok)] += 1
        if not ok and len(ex) < 8: ex.append((line, z, u, T))
print(dict(sorted(C.items())))
print("UNCERT", ex)

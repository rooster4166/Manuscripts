"""E-B(2): a candidate strengthened hypothesis for the L-infinity residual.
For each residual instance (as linf.py) and each target u in N(z): does K - zu have a Lovász
decomposition whose l-path lies in B AND whose far end y is not in N(u)?  If yes for some u, that
Case I step is safe for every such decomposition (Proposition 4.1: y not in N(u) => P* untouched)."""
import sys, subprocess, collections
import networkx as nx
import tf
n = int(sys.argv[1])
C = collections.Counter(); ex = []
gs = subprocess.run(['nauty-geng', '-cq', str(n)], capture_output=True, text=True).stdout.split()
for s in gs:
    K = tf.from_g6(s); ev = tf.evens(K)
    if len(ev) != 1: continue
    z = ev[0]; H = tf.to_nx(K)
    for l in K:
        if tf.deg(K, l) != 1: continue
        c = next(iter(K[l]))
        if tf.deg(K, c) % 2 == 0: continue
        dist = nx.single_source_shortest_path_length(H, c)
        if dist.get(z) != 3 or any(dist[u] != 2 for u in K[z]): continue
        if not (tf.deg(K, z) >= 4 or any(b in K[a] for a in K[z] for b in K[z])): continue
        B = {l, c} | set(K[c])
        good_u = []
        for u in sorted(K[z]):
            K1 = tf.rem(K, (z, u)); b1 = tf.lovasz_b(K1)
            for D1 in tf.decomps(K1, b1, l, region=B):
                P = tf.Qc(D1, l); y = P[-1] if P[0] == l else P[0]
                if y not in K[u]:
                    good_u.append(u); break
        C["some u has a far-end-safe D'" if good_u else "NO u"] += 1
        C[("#u with far-end-safe D'", len(good_u), "of", len(K[z]))] += 1
        if not good_u and len(ex) < 5: ex.append((s, l, c, z))
for k, v in sorted(C.items(), key=str): print(k, v)
for e in ex: print("EX", e)

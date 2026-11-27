"""E-B: the L-infinity residual (route-descent §V.4c), exhaustively at order n.
K connected, a leaf l with neighbour c, exactly one positive even vertex z, d(c,z) = 3, every
neighbour of z at distance 2 from c, and deg z >= 4 or z on a triangle.  B = {l} + N[c].
For u in N(z), K' = K - zu (even vertex u).  For every Lovász decomposition D' of K' whose
l-path P* lies in B, run the forced Fan chain z -> u and record
  (y in N(u), chain reaches y, result's l-path in B)   where y is the far end of P*.
Also: does some (u, D') succeed (the induction step closes)?"""
import sys, subprocess, collections
import networkx as nx
import tf
n = int(sys.argv[1])
C = collections.Counter(); ex = []
gs = subprocess.run(['nauty-geng', '-cq', str(n)], capture_output=True, text=True).stdout.split()
ninst = 0
for s in gs:
    K = tf.from_g6(s)
    ev = tf.evens(K)
    if len(ev) != 1: continue
    z = ev[0]
    H = tf.to_nx(K)
    for l in K:
        if tf.deg(K, l) != 1: continue
        c = next(iter(K[l]))
        if tf.deg(K, c) % 2 == 0: continue
        dist = nx.single_source_shortest_path_length(H, c)
        if dist.get(z) != 3 or any(dist[u] != 2 for u in K[z]): continue
        tri = any(b in K[a] for a in K[z] for b in K[z])
        if not (tf.deg(K, z) >= 4 or tri): continue
        ninst += 1
        B = {l, c} | set(K[c]); bK = tf.lovasz_b(K)
        assert tf.exists(K, bK, l, region=B) is not None, ("GL fails!", s, l)
        closes = False; per = collections.Counter()
        for u in sorted(K[z]):
            K1 = tf.rem(K, (z, u)); b1 = tf.lovasz_b(K1)
            for D1 in tf.decomps(K1, b1, l, region=B):
                Ps = tf.Qc(D1, l); y = Ps[-1] if Ps[0] == l else Ps[0]
                D2, chain, Pfin = tf.fan_results(K, D1, z, u)[0]
                ok = set(tf.Qc(D2, l)) <= B
                hit = y in chain
                per[(y in K[u], hit, ok)] += 1
                closes |= ok
        for k, v in per.items(): C[k] += v
        C["instance closes" if closes else "instance DOES NOT close"] += 1
        if not closes and len(ex) < 5: ex.append((s, l, c, z))
print("order", n, "instances", ninst)
print("key = (far end y in N(u), chain reaches y, result in B)")
for k, v in sorted(C.items(), key=str): print(k, v)
for e in ex: print("EX", e)

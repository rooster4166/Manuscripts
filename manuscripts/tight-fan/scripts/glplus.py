"""E-B(3): the strengthened leaf statement GL+ (candidate inductive invariant for L-infinity).
K connected, a leaf l with neighbour c, exactly one even vertex g (g != c), B = {l} + N[c].
GL+ : some Lovász decomposition has its l-path inside B and its far end y NOT adjacent to g.
(In a Case I step z -> u of the GL induction, u is the even vertex of K - zu, and GL+ for K - zu is
exactly the condition that makes the step safe, Proposition 4.1.)  Classified by dist(c, g)."""
import sys, subprocess, collections
import networkx as nx
import tf
n = int(sys.argv[1])
C = collections.Counter(); ex = collections.defaultdict(list)
gs = subprocess.run(['nauty-geng', '-cq', str(n)], capture_output=True, text=True).stdout.split()
for s in gs:
    K = tf.from_g6(s); ev = tf.evens(K)
    if len(ev) != 1: continue
    g = ev[0]; H = tf.to_nx(K)
    for l in K:
        if tf.deg(K, l) != 1: continue
        c = next(iter(K[l]))
        if c == g or tf.deg(K, c) % 2 == 0: continue
        d = nx.shortest_path_length(H, c, g)
        B = {l, c} | set(K[c]); b = tf.lovasz_b(K)
        ok = False; any_gl = False
        for D in tf.decomps(K, b, l, region=B):
            any_gl = True
            P = tf.Qc(D, l); y = P[-1] if P[0] == l else P[0]
            if y not in K[g]:
                ok = True; break
        key = (f"d(c,g)={min(d,3) if d < 3 else '>=3'}",)
        C[key + ("GL holds" if any_gl else "GL FAILS",)] += 1
        C[key + ("GL+ holds" if ok else "GL+ FAILS",)] += 1
        if not ok and len(ex[key]) < 4: ex[key].append((s, l, c, g))
for k, v in sorted(C.items()): print(k, v)
for k, v in ex.items(): print("EX", k, v)

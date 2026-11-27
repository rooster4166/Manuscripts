"""cross-check tf.decomps (avoid pruning) against l1s.c 'ed' mode on all graphs of order <= 7"""
import subprocess, sys, itertools, random
import tf
random.seed(1)
lines = []; qs = []
for n in (5, 6, 7):
    gs = subprocess.run(['nauty-geng', '-cq', str(n)], capture_output=True, text=True).stdout.split()
    for s in gs:
        G = tf.from_g6(s)
        if len(tf.evens(G)) > 1: continue
        E = tf.edges(G)
        for c in G:
            if tf.deg(G, c) % 2 == 0: continue
            for _ in range(2):
                A = [v for v in G if v != c and random.random() < 0.3]
                mask = sum(1 << a for a in A)
                lines.append(f"{n} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + f" {c} {mask}")
                qs.append((G, c, frozenset(A)))
out = subprocess.run(['./l1s', 'ed'], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout.split()
assert len(out) == len(qs), (len(out), len(qs))
mis = 0
for (G, c, A), o in zip(qs, out):
    r = tf.exists(G, tf.lovasz_b(G), c, A) is not None
    if int(o) != int(r): mis += 1; print("MISMATCH", G, c, A, o, r)
print("queries", len(qs), "mismatches", mis)

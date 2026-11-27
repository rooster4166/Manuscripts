"""E-E(2): the one-step derived class.  For every admissible instance (G, c, A) with c not in N(g)
and every u in N(g), is (G - gu, c, A) good?  (|A| <= K, order n, via l1s 'ed'.)  Classified by
whether (G, c, A) is blocked and whether u is free of A minus g (then (G - gu, c, A) is admissible)."""
import sys, subprocess, itertools, collections
import tf
n = int(sys.argv[1]); K = int(sys.argv[2])
gs = subprocess.run(['nauty-geng', '-cq', str(n)], capture_output=True, text=True).stdout.split()
rows = []; lines = []
for s in gs:
    G = tf.from_g6(s); ev = tf.evens(G)
    if len(ev) != 1: continue
    g = ev[0]; Ng = set(G[g])
    for c in G:
        if tf.deg(G, c) % 2 == 0 or c in Ng: continue
        cand = [v for v in G if v != c and v not in G[c] and v not in Ng and tf.deg(G, v) > 0]
        for k in range(1, K + 1):
            for S in itertools.combinations(cand, k):
                A = frozenset(S)
                blocked = all((set(G[x]) & A) - {g} for x in Ng)
                for u in sorted(Ng):
                    G1 = tf.rem(G, (g, u)); E = tf.edges(G1)
                    free = not ((set(G[u]) & A) - {g})
                    rows.append((s, g, c, A, u, blocked, free, u in G[c]))
                    lines.append(f"{n} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + f" {c} {sum(1 << a for a in A)}")
out = subprocess.run(['./l1s', 'ed', '20000000'], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout.split()
C = collections.Counter(); ex = []
per = collections.defaultdict(list)
for r, o in zip(rows, out):
    s, g, c, A, u, blocked, free, inc = r
    C[("blocked" if blocked else "unblocked", "u free" if free else "u not free", "u in N(c)" if inc else "u out", "good" if o == "1" else "BAD")] += 1
    per[(s, g, c, A)].append(o == "1")
    if o != "1" and not free and len(ex) < 6: ex.append((s, g, c, sorted(A), u))
C2 = collections.Counter(("all u good" if all(v) else "some u good" if any(v) else "NO u good") for v in per.values())
for k, v in sorted(C.items()): print(k, v)
for k, v in sorted(C2.items()): print("per instance:", k, v)
for e in ex: print("EX-bad", e)

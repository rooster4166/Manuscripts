"""E-A (fast): blocked L1* residuals (irreducible one level deep), order n, |A| <= K.
For each u in N(g): is the (inadmissible) instance (G - gu, c, A) good?  Queries go to l1s 'ed'.
If u is not in N(c) and (G - gu, c, A) is good, the protected transfer (l1star Lemma 2.4) makes
(G, c, A) good: the hypothesis-side failure is then only a failure of admissibility."""
import sys, collections, subprocess
import tf, resid
n = int(sys.argv[1]); K = int(sys.argv[2]); mode = sys.argv[3] if len(sys.argv) > 3 else 'irr'
inst = []
for line, G, g, c, A, irr in resid.residuals(n, K, amax=(mode == 'max')):
    if mode == 'irr' and not irr: continue
    inst.append((line, G, g, c, A))
queries = []
for k, (line, G, g, c, A) in enumerate(inst):
    for u in sorted(G[g]):
        G1 = tf.rem(G, (g, u)); E = tf.edges(G1)
        mask = sum(1 << a for a in A)
        queries.append((k, u, f"{n} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + f" {c} {mask}"))
out = subprocess.run(['./l1s', 'ed', '20000000'], input="\n".join(q[2] for q in queries) + "\n",
                     capture_output=True, text=True).stdout.split()
assert len(out) == len(queries)
res = collections.defaultdict(dict)
for (k, u, _), o in zip(queries, out): res[k][u] = int(o)
C = collections.Counter(); ex = []
for k, (line, G, g, c, A) in enumerate(inst):
    key = ("gA" if g in A else "sep", f"d(g)={len(G[g])}")
    C[key] += 1
    r = res[k]
    out_c = [u for u in r if r[u] == 1 and u not in G[c]]
    in_c = [u for u in r if r[u] == 1 and u in G[c]]
    tag = "good-u-outside-N(c)" if out_c else ("good-u-only-in-N(c)" if in_c else "NO-good-u")
    if any(v == 2 for v in r.values()): tag += "+budget"
    C[key + (tag,)] += 1
    if not out_c and len(ex) < 12: ex.append((line, g, c, sorted(A), r))
for kk, v in sorted(C.items()): print(kk, v)
for e in ex: print("EX", e)

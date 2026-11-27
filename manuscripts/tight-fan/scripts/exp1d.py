"""E-A(d): the tight transfer in blocked residuals.  For each irreducible blocked instance and each
u in N(g) with (G - gu, c, A) good, run the forced Fan chain g -> u from EVERY good D' of G - gu
(plain graph, no leaf) and record whether the result is good, and whether the chain passed c."""
import sys, collections
import tf, resid
n = int(sys.argv[1]); K = int(sys.argv[2]); mode = sys.argv[3] if len(sys.argv) > 3 else 'irr'
C = collections.Counter(); ex = []
for line, G, g, c, A, irr in resid.residuals(n, K, amax=(mode == 'max')):
    if mode == 'irr' and not irr: continue
    key = ("gA" if g in A else "sep", f"d(g)={len(G[g])}")
    best = 0; tot = 0; okc = collections.Counter()
    for u in sorted(G[g]):
        G1 = tf.rem(G, (g, u)); b1 = tf.lovasz_b(G1)
        for D1 in tf.decomps(G1, b1, c, A):
            tot += 1
            outs = tf.fan_results(G, D1, g, u)
            assert len({tf.canon(o[0]) for o in outs}) == 1, 'Fan image not unique'
            D2, chain, P = outs[0]
            ok = not (set(tf.Qc(D2, c)) & A)
            thru = c in chain
            okc[(u in G[c], thru, ok)] += 1
    for kk, v in okc.items(): C[key + kk] += v
    if not any(k[2] for k in okc) and len(ex) < 6: ex.append((line, g, c, sorted(A), dict(okc)))
    C[key + ("instance-some-ok" if any(k[2] for k in okc) else "instance-NONE-ok",)] += 1
print("key = (type, d(g), u in N(c), chain passes c, result good)")
for kk, v in sorted(C.items(), key=str): print(kk, v)
for e in ex: print("EX", e)

"""E-A at order n, irreducible blocked residuals only: is (G - gu, c, A) good for some u?
And does the forced Fan chain from a good D' of G - gu always preserve goodness?"""
import sys, collections, time
import tf, resid
n = int(sys.argv[1]); K = int(sys.argv[2]); amax = len(sys.argv) > 3 and sys.argv[3] == 'max'
C = collections.Counter(); ex = []
t0 = time.time()
for line, G, g, c, A, irr in resid.residuals(n, K, amax):
    if not irr: continue
    b = tf.lovasz_b(G)
    key = ("gA" if g in A else "sep", f"d(g)={len(G[g])}", f"d(c)={len(G[c])}")
    C[key] += 1
    goodu = []; pres = True
    for u in sorted(G[g]):
        G1 = tf.rem(G, (g, u)); b1 = tf.lovasz_b(G1)
        D1 = tf.exists(G1, b1, c, A)
        if D1 is not None:
            goodu.append(u)
            D2 = tf.fan_results(G, D1, g, u)[0][0]
            if set(tf.Qc(D2, c)) & A:
                pres = False
    C[key + ("some-u-good" if goodu else "NO-u-good",)] += 1
    C[key + ("u-in-N(c)" if any(u in G[c] for u in goodu) else "u-outside-N(c)" if goodu else "-",)] += 1
    if not pres: C[key + ("fan-broke",)] += 1
    if not goodu and len(ex) < 10: ex.append((line, g, c, sorted(A)))
for k, v in sorted(C.items()): print(k, v)
for e in ex: print("EX-NOGOOD", e)
print("time", round(time.time() - t0))

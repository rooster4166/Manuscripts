"""E-A(f): existence form of E26(A)'s sufficient condition, with early stopping.
For each irreducible blocked instance in which every good target lies in N(c) (the tight case),
search for u in N(g) cap N(c) and a good D' of G - gu satisfying the condition of Theorem 4.2
(the path through cu is Q_c with terminal edge uc, or its c-side end lies outside N(u) + {g}).
Every hit is checked: the forced Fan image is verified to be good."""
import sys, collections
import tf, resid
def cside_end(D, c, u):
    for P in D:
        for i in range(len(P) - 1):
            if {P[i], P[i + 1]} == {c, u}:
                if P[i] == c: return P[0], (i == 0)
                else: return P[-1], (i + 1 == len(P) - 1)
    raise ValueError
n = int(sys.argv[1]); K = int(sys.argv[2])
C = collections.Counter(); ex = []
for line, G, g, c, A, irr in resid.residuals(n, K):
    if not irr: continue
    key = ("gA" if g in A else "sep", f"d(g)={len(G[g])}")
    found = False; tight_only = True
    for u in sorted(G[g]):
        if u in G[c]: continue
        G1 = tf.rem(G, (g, u))
        if tf.exists(G1, tf.lovasz_b(G1), c, A) is not None: tight_only = False; break
    if not tight_only:
        C[key + ("has good u outside N(c)",)] += 1; continue
    for u in sorted(G[g]):
        if u not in G[c]: continue
        G1 = tf.rem(G, (g, u)); b1 = tf.lovasz_b(G1)
        for D1 in tf.decomps(G1, b1, c, A):
            e, term = cside_end(D1, c, u)
            if term or (e not in G1[u] and e != g):
                D2 = tf.fan_results(G, D1, g, u)[0][0]
                assert not (set(tf.Qc(D2, c)) & A)
                found = True; break
        if found: break
    C[key + ("tight", "condition met by some good D'" if found else "CONDITION NEVER MET")] += 1
    if not found and len(ex) < 10: ex.append((line, g, c, sorted(A)))
for k, v in sorted(C.items()): print(k, v)
for e in ex: print("EX", e)

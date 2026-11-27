"""E-A(e): the provable sufficient condition in the tight L1* transfer.
For an irreducible blocked instance, u in N(g) cap N(c), and a good D' of G - gu (Q_c avoids A):
  SC(D') : the path of D' through the edge cu is Q_c with terminal edge uc, or its end on c's side
           (reading away from u) lies outside N(u) + {g}.
Tight Fan lemma: SC(D') => the protected transfer succeeds.  We record SC, chain-avoids-c, result."""
import sys, collections
import tf, resid
n = int(sys.argv[1]); K = int(sys.argv[2]); mode = sys.argv[3] if len(sys.argv) > 3 else 'irr'
C = collections.Counter(); ex = []
def cside_end(D, c, u):
    for P in D:
        for i in range(len(P) - 1):
            if {P[i], P[i + 1]} == {c, u}:
                if P[i] == c: return P[0], (i == 0)          # read from P[0] .. c u
                else: return P[-1], (i + 1 == len(P) - 1)   # .. u c .. P[-1]
    raise ValueError
for line, G, g, c, A, irr in resid.residuals(n, K, amax=(mode == 'max')):
    if mode == 'irr' and not irr: continue
    key = ("gA" if g in A else "sep", f"d(g)={len(G[g])}")
    inst_sc = False; inst_ok = False; tight = False
    for u in sorted(G[g]):
        if u not in G[c]: continue
        G1 = tf.rem(G, (g, u)); b1 = tf.lovasz_b(G1)
        for D1 in tf.decomps(G1, b1, c, A):
            tight = True
            e, term = cside_end(D1, c, u)
            sc = term or (e not in G1[u] and e != g)
            D2, chain, P = tf.fan_results(G, D1, g, u)[0]
            ok = not (set(tf.Qc(D2, c)) & A)
            C[key + ("SC" if sc else "noSC", "avoid" if c not in chain else "hit", ok)] += 1
            assert (not sc) or ok, "tight Fan lemma violated?!"
            inst_sc |= sc; inst_ok |= ok
    if tight:
        C[key + ("instance", "SC-some-D'" if inst_sc else ("ok-but-no-SC" if inst_ok else "NO-OK"))] += 1
        if not inst_sc and len(ex) < 5: ex.append((line, g, c, sorted(A)))
for kk, v in sorted(C.items(), key=str): print(kk, v)
for e in ex: print("EX-noSC", e)

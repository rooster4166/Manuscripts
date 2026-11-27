"""E-A: Lovász Case I at the even vertex of blocked L1* instances.
For each blocked instance (G, c, A) and each u in N(g), with G' = G - gu:
  good'   : is (G', c, A) good (Q_c avoids A), although inadmissible?
  fanok   : among Lovász D' of G' with Q_c avoiding A, does the (forced) Fan chain t=g -> u
            give a good decomposition of G?  (all D' tested; 'all'/'some'/'none')
  hypo    : among Lovász D' of G' with Q_c avoiding A minus N(u) (the admissible hypothesis),
            fraction whose Fan image is good.
"""
import sys, collections
import tf, resid
n = int(sys.argv[1]); K = int(sys.argv[2]) if len(sys.argv) > 2 else 2
C = collections.Counter(); ex = collections.defaultdict(list)
for line, G, g, c, A, irr in resid.residuals(n, K):
    b = tf.lovasz_b(G)
    good = tf.exists(G, b, c, A) is not None
    assert good
    row = []
    anyfix = False; anyfix_hypo = False
    for u in sorted(G[g]):
        G1 = tf.rem(G, (g, u)); b1 = tf.lovasz_b(G1)
        A1 = frozenset(a for a in A if a not in G1[u])
        nh = nok = 0; nstrict = nstrict_ok = 0
        for D1 in tf.decomps(G1, b1, c, A1):
            nh += 1
            outs = tf.fan_results(G, D1, g, u)
            assert len({tf.canon(o[0]) for o in outs}) == 1, "Fan not deterministic?"
            D2 = outs[0][0]
            ok = not (set(tf.Qc(D2, c)) & A)
            nok += ok
            strict = not (set(tf.Qc(D1, c)) & A)
            nstrict += strict; nstrict_ok += (strict and ok)
        row.append((u, nh, nok, nstrict, nstrict_ok))
        anyfix |= nstrict > 0
        anyfix_hypo |= nok > 0
    key = ("irr" if irr else "red", "gA" if g in A else "sep", f"d(g)={len(G[g])}")
    C[key + ("goodG'-some-u" if anyfix else "goodG'-no-u",)] += 1
    C[key + ("fan-from-hyp-some" if anyfix_hypo else "fan-from-hyp-none",)] += 1
    C[key + ("hyp-all-ok" if any(r[1] == r[2] and r[1] > 0 for r in row) else "hyp-not-all",)] += 1
    if not anyfix and len(ex[key]) < 3: ex[key].append((line, g, c, sorted(A), row))
for k, v in sorted(C.items()): print(k, v)
for k, v in ex.items(): print("EX", k, v)

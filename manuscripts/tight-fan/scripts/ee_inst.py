"""E-D: CP(3)+apex and the double K4.  For each EE pair (z, u) (z the even vertex, u in N(z)),
the L1* instances EE needs: (K - uz, z, {u}) and, for w in N(u) cap N(z), the triangle instance
(K - {uz, uw, wz}, w, {u, z}).  For each: is it blocked?  For each Case I target x in N(g):
is (G - gx, c, A) good (admissible or not), is x in N(c) (tight), and does some good D' of G - gx
satisfy the tight sufficient condition (c-side end of the cx-path outside N(x) + {g})?"""
import sys, collections
import tf
def cside_end(D, c, u):
    for P in D:
        for i in range(len(P) - 1):
            if {P[i], P[i + 1]} == {c, u}:
                if P[i] == c: return P[0], (i == 0)
                else: return P[-1], (i + 1 == len(P) - 1)
def analyse(G, c, A):
    ev = tf.evens(G); g = ev[0] if ev else None
    if g is None: return "all-odd"
    b = tf.lovasz_b(G)
    good = tf.exists(G, b, c, frozenset(A)) is not None
    adm = not (set(A) & (set(G[c]) | {c} | set(G[g])))
    blocked = (c not in G[g]) and all((set(G[x]) & set(A)) - {g} for x in G[g])
    rows = []
    for x in sorted(G[g]):
        G1 = tf.rem(G, (g, x)); b1 = tf.lovasz_b(G1)
        goods = list(tf.decomps(G1, b1, c, frozenset(A))) if tf.deg(G1, c) % 2 == 1 else []
        sc = 0; ok = 0
        for D1 in goods:
            if x in G[c]:
                e, term = cside_end(D1, c, x)
                sc += term or (e not in G1[x] and e != g)
            D2 = tf.fan_results(G, D1, g, x)[0][0]
            ok += not (set(tf.Qc(D2, c)) & set(A))
        rows.append((x, "inN(c)" if x in G[c] else "out", len(goods), ok, sc))
    return dict(good=good, admissible=adm, blocked=blocked, g=g, targets=rows)
for name, s in (("CP(3)+apex", "F]~vw"), ("double K4", "FQhVw")):
    K = tf.from_g6(s); z = tf.evens(K)[0]
    print("==", name, s, "z =", z, {v: sorted(K[v]) for v in K})
    for u in sorted(K[z]):
        print(" pair (z,u) =", (z, u), "|N(u)&N(z)| =", len(K[u] & K[z]))
        G = tf.rem(K, (u, z)); print("   (K-uz, z, {u}):", analyse(G, z, [u]))
        for w in sorted(K[u] & K[z]):
            G = tf.rem(K, (u, z), (u, w), (w, z))
            print("   tri w=%d:" % w, analyse(G, w, [u, z]))

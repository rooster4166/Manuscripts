"""A24 (a): the authors' own exp1d.py per-transfer logic (tf.decomps + tf.fan_results, as in
manuscripts/tight-fan/scripts/exp1d.py at 39f2d37), run on ONE instance (graph6, g, c, A) to show
that their pipeline records chain-through-c transfers with a good result at order 9.
usage: python3 a_exp1d_single.py TFDIR g6 g c a1,a2"""
import sys, collections
sys.path.insert(0, sys.argv[1])
import tf
G = tf.from_g6(sys.argv[2]); g = int(sys.argv[3]); c = int(sys.argv[4])
A = frozenset(int(x) for x in sys.argv[5].split(','))
okc = collections.Counter()
for u in sorted(G[g]):
    G1 = tf.rem(G, (g, u)); b1 = tf.lovasz_b(G1)
    for D1 in tf.decomps(G1, b1, c, A):
        outs = tf.fan_results(G, D1, g, u)
        D2, chain, P = outs[0]
        ok = not (set(tf.Qc(D2, c)) & A)
        okc[(u, u in G[c], c in chain, ok, len(outs))] += 1
print("key = (u, u in N(c), chain passes c, result good, #Fan images)")
for k, v in sorted(okc.items()): print(k, v)

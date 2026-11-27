"""A24 (a), order 9: find and print the first irreducible blocked L1* instance (|A| <= 2, same
filter as a_dichotomy.py) with a good D' of G - gu, u in N(c), whose forced Fan chain g -> u passes
through c and whose result is nevertheless GOOD (Q_c avoids A).  Cross-checks the result with the
authors' tf.fan_moves (path given as argv[1]) and with mylib's checker.
usage: python3 a_counterexample.py TFDIR [how_many]
"""
import sys, itertools
sys.path.insert(0, sys.argv[1])
import tf
import mylib as M
sys.argv = [sys.argv[0], '9', '2'] + sys.argv[2:3]
how_many = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2:] and sys.argv[2] != '2' else 3
import importlib.util
spec = importlib.util.spec_from_file_location('ad', __file__.replace('a_counterexample.py', 'a_dichotomy.py'))
# re-use only the instance generator of a_dichotomy.py (its main loop is not executed)
src = open(spec.origin).read().split("\nC = collections.Counter(); EX = []")[0]
ns = {'__name__': 'ad'}
sys.argv = ['a_dichotomy.py', '9', '2']
exec(compile(src, spec.origin, 'exec'), ns)
found = 0
for s, G, g, c, A, irr in ns['instances']():
    if not irr:
        continue
    for u in sorted(G[g] & G[c]):
        G1 = M.deledge(G, (g, u)); b1 = M.lov(G1)
        okf = (lambda P, A=A: not ((P[0] == c or P[-1] == c) and (set(P) & A)))
        for D1 in M.decomps_pg(G1, b1, first_edges=[(c, y) for y in sorted(G1[c])], path_ok=okf):
            st, ch, ix = M.forced_chain(D1, g, u)
            if c not in ch:
                continue
            D2 = M.exec_chain(D1, ch, ix, u)
            Qc2 = M.path_with_end(D2, c)
            if set(Qc2) & A:
                continue
            # independent checks
            assert M.verify(G1, D1, b1) and not (set(M.path_with_end(D1, c)) & A)
            assert M.verify(G, D2, M.lov(G))
            tfr = tf.fan_moves([tuple(P) for P in D1], g, u)
            assert len(tfr) == 1 and M.canon(tfr[0][0]) == M.canon(D2)
            print("COUNTEREXAMPLE to 'chain through c => bad'")
            print("  G =", s, "edges", M.edgelist(G))
            print("  g =", g, "d(g) =", len(G[g]), "c =", c, "A =", sorted(A), "u =", u,
                  "type", "gA" if g in A else "sep")
            print("  D' (Lovász decomposition of G - gu, Q_c avoids A):", D1)
            print("  Q_c in D':", M.path_with_end(D1, c))
            print("  forced chain:", ch)
            print("  result D:", D2)
            print("  Q_c in D:", Qc2, " meets A:", bool(set(Qc2) & A))
            found += 1
            break
        if found >= how_many:
            break
    if found >= how_many:
        break

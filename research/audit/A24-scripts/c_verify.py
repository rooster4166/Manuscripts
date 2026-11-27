"""A24 (c): independent verification of the PTM_2 decompositions printed by ptmwalk_audit.py
(SOL lines).  Own graph6 decoder and checker (mylib), nothing from tf.py.
For each SOL line: G = (graph6 of G - F) + a1b1 + a2b2; check that D is a path decomposition of G,
that b = d mod 2 everywhere (Lovász), that each F-edge is terminal at one of its ends, and that
the two F-edges lie on different paths.  Also checks that the reported walk is a path of G from y
to a avoiding b and x, and that it is NOT admissible (some inner vertex in N(x)).
"""
import sys, ast
import mylib as M

ok = bad = 0
for line in open(sys.argv[1]):
    if not line.startswith('SOL'):
        continue
    w = line.split(None, 6)
    g6s = w[1]; a1, b1, a2, b2 = map(int, w[2:6])
    rest = w[6]
    # rest = "(a, b, x, y) (walk) [paths]"
    i1 = rest.index(')') + 1
    abxy = ast.literal_eval(rest[:i1].strip())
    rest2 = rest[i1:].strip()
    i2 = rest2.index(')') + 1
    walk = ast.literal_eval(rest2[:i2].strip())
    D = ast.literal_eval(rest2[i2:].strip())
    G = M.addedge(M.g6(g6s), (a1, b1), (a2, b2))
    good = M.verify(G, D, M.lov(G))

    def term(e):
        p, q = e
        for i, P in enumerate(D):
            if (P[0] == p and P[1] == q) or (P[-1] == p and P[-2] == q):
                return i
            if (P[0] == q and P[1] == p) or (P[-1] == q and P[-2] == p):
                return i
        return None
    i1_, i2_ = term((a1, b1)), term((a2, b2))
    good = good and i1_ is not None and i2_ is not None and i1_ != i2_
    a, b, x, y = abxy
    walk_ok = (walk[0] == y and walk[-1] == a and b not in walk and x not in walk
               and all(walk[j + 1] in G[walk[j]] for j in range(len(walk) - 1))
               and len(set(walk)) == len(walk))
    nonadm = any(walk[j] in G[x] for j in range(1, len(walk) - 1))
    if good and walk_ok and nonadm:
        ok += 1
    else:
        bad += 1
        print("BAD", line.strip(), good, walk_ok, nonadm)
print("verified", ok, "bad", bad)

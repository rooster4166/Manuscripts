"""admissible.py: which base conditions are single L1*-admissible avoidance statements?
For each shape D and every labelling with x1y2, x2y3 in E(B), the base graph M restricted to
U + z (z a leaf at y1, g = x3 the even vertex).  A condition 'P_c avoids A' is L1*-admissible if
A misses N_M[c] and N_M(g) (g itself may lie in A).  Conditions (E1) z-path avoids x1;
(E1') P_y2, P_y3 avoid z; (E2) P_y2 avoids x2; (E3) P_y3 avoids x3; (E4') P_y2 avoids y3
(a strengthening of E4); (E5) P_x2 avoids y3; (E7) P_x1 avoids y2."""
import itertools
SH = {'empty': [], 'K2': [(0, 1)], 'P3': [(0, 1), (1, 2)], 'K3': [(0, 1), (1, 2), (0, 2)],
      'C4': [(0, 1), (1, 2), (2, 3), (0, 3)]}
for sh, D in SH.items():
    D = set(frozenset(e) for e in D)
    best = None
    hist = {}
    for p in itertools.permutations(range(6)):
        x1, y1, x2, y2, x3, y3 = p
        B = lambda a, b: a != b and frozenset((a, b)) not in D
        if not (B(x1, y2) and B(x2, y3)):
            continue
        z = 'z'
        def adj(a, b):
            if a == z or b == z:
                return {a, b} == {z, y1}
            if {a, b} in ({x1, y2}, {x2, y3}):
                return False
            return B(a, b)
        N = lambda v: {w for w in list(range(6)) + [z] if adj(v, w)}
        g = x3
        def ok(c, A):
            return not (A & (N(c) | {c} | N(g)))
        conds = {'E1': ok(z, {x1}), "E1'": ok(y2, {z}) and ok(y3, {z}), 'E2': ok(y2, {x2}),
                 'E3': ok(y3, {x3}), "E4'": ok(y2, {y3}), 'E5': ok(x2, {y3}), 'E7': ok(x1, {y2})}
        bad = tuple(k for k, v in conds.items() if not v)
        hist[bad] = hist.get(bad, 0) + 1
        if best is None or len(bad) < len(best):
            best = bad
    print(sh, 'fewest inadmissible:', best, '| most common:',
          sorted(hist.items(), key=lambda kv: -kv[1])[:3])

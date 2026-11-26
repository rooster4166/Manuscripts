"""Sec. 8 'Where the method stops' (1): root hub (i) with |N(y) & T| = 3.
Shape: single receipt from p, two grouped receipts (donor adversarial or, for 'control',
chosen), then the three donations r->s1, r->s2, r->y in any order."""
import itertools
from adversarial import Cert, Fail, mkadj
r, T, y = 0, [1, 2, 3, 4, 5], 'y'; U = [r] + T
Ny = {1, 2, 3}
forced = [(r, t) for t in T] + [(r, y)] + [(y, t) for t in Ny]
forb = [(y, t) for t in T if t not in Ny]
adj = mkadj(forced, forb)
def start():
    b = {v: 1 for v in U + [y]}; b[r] = 2; b[y] = 0
    return Cert(U + [y], b, [(r, t) for t in T] + [(r, y)], adj)
def finish_ok(c, Z):
    S = [t for t in T if t not in Z]
    for order in itertools.permutations(S + [y]):
        d = c
        try:
            for v in order: d = d.single(v, r, None)
            return True
        except Fail: pass
    return False
def outcome(p, control):
    c1 = start().single(r, p, None)
    res = []
    for z2, c2 in c1.step(r, [t for t in T if t != p], None):
        for z3, c3 in c2.step(r, [t for t in T if t not in (p, z2)], None):
            res.append(finish_ok(c3, {p, z2, z3}))
    return any(res) if control else all(res)
print("adversarial donors: some first donor p succeeds against every z2, z3:", any(outcome(p, False) for p in T))
print("controlled donors:  some p and some z2, z3 succeed:", any(outcome(p, True) for p in T))

"""Audit A9: adversarial replay of every step table of d6-frontier.tex in the symbolic model
of adversarial.py (worst-case adjacency, every grouped donor branched)."""
import itertools, sys
from adversarial import Cert, Fail, mkadj, finish

def subsets(S, kmax, kmin=0):
    S = list(S)
    for k in range(kmin, min(kmax, len(S)) + 1):
        yield from (set(c) for c in itertools.combinations(S, k))

def grouped(c, recv, donors, bound, cont):
    n = 0
    for d, c2 in c.step(recv, donors, bound):
        n += cont(c2, d)
    return n

# ---------------------------------------------------------------- Thm 4.1(i)
def roothub_i():
    r, T, y = 0, [1, 2, 3, 4, 5], 'y'
    U = [r] + T
    total = 0
    for Ny in subsets(T, 2):
        forced = [(r, t) for t in T] + [(r, y)] + [(y, t) for t in Ny]
        forb = [(y, t) for t in T if t not in Ny]
        adj = mkadj(forced, forb)
        held = [(r, t) for t in T] + [(r, y)]
        b = {v: 1 for v in U + [y]}; b[r] = 2; b[y] = 0
        c0 = Cert(U + [y], b, held, adj)
        ny = sorted(Ny)
        p = ny[0] if ny else T[0]
        pp = ny[1] if len(ny) > 1 else None
        c1 = c0.single(r, p, 0)
        def after2(c2, z2):
            def after3(c3, z3):
                Z = {p, z2, z3}
                S = [t for t in T if t not in Z]
                S.sort(key=lambda s: s != pp)
                c4 = c3.single(S[0], r, 4)
                c5 = c4.single(S[1], r, 3)
                c6 = c5.single(y, r, 2)
                finish(c6, U, r, [y]); return 1
            return grouped(c2, r, [t for t in T if t not in (p, z2)], 2, after3)
        total += grouped(c1, r, [t for t in T if t != p], 1, after2)
    return total

# ---------------------------------------------------------------- Thm 4.1(ii)
def roothub_ii():
    r, T, q, a, b_ = 0, [1, 2, 3, 4, 5], 1, 'a', 'b'
    U = [r] + T
    total = 0
    for Na in subsets(T, 2):
        forced = [(r, t) for t in T if t != q] + [(r, a), (r, b_), (a, b_)] + [(a, t) for t in Na]
        forb = [(r, q), (b_, q)] + [(a, t) for t in T if t not in Na]
        adj = mkadj(forced, forb)
        held = [(r, t) for t in T if t != q] + [(r, a), (r, b_), (a, b_)]
        b = {v: 1 for v in U + [a, b_]}; b[r] = 2; b[q] = 0
        c = Cert(U + [a, b_], b, held, adj)
        Tq = [t for t in T if t != q]
        na = sorted(set(Na) & set(Tq))
        z1 = na[0] if na else Tq[0]
        w = na[1] if len(na) > 1 else None
        c = c.single(r, b_, 0); c = c.single(b_, a, 0); c = c.single(r, z1, 0)
        def after4(c4, z2):
            Z = {q, z1, z2}
            S = [t for t in T if t not in Z]; S.sort(key=lambda s: s != w)
            c5 = c4.single(S[0], r, 4); c6 = c5.single(S[1], r, 3); c7 = c6.single(a, r, 2)
            finish(c7, U, r, [a, b_]); return 1
        total += grouped(c, r, [t for t in Tq if t != z1], 1, after4)
    return total

# ---------------------------------------------------------------- Thm 4.1(iii)
def roothub_iii():
    r, NT, q1, q2, a, b_ = 0, [1, 2, 3], 4, 5, 'a', 'b'
    T = NT + [q1, q2]; U = [r] + T
    total = 0
    for Na in subsets(NT, 1):
        forced = [(r, t) for t in NT] + [(r, a), (r, b_), (a, b_)] + [(a, t) for t in Na]
        forb = [(r, q1), (r, q2), (b_, q2)] + [(a, t) for t in NT if t not in Na]
        adj = mkadj(forced, forb)
        held = [(r, t) for t in NT] + [(r, a), (r, b_), (a, b_)]
        b = {v: 1 for v in U + [a, b_]}; b[q1] = 2; b[q2] = 0
        c = Cert(U + [a, b_], b, held, adj)
        z1 = sorted(Na)[0] if Na else NT[0]
        c = c.single(r, b_, 0); c = c.single(b_, a, 0); c = c.single(r, z1, 0)
        def after4(c4, z2):
            s = [t for t in NT if t not in (z1, z2)][0]
            c5 = c4.single(s, r, 3); c6 = c5.single(a, r, 2)
            finish(c6, U, r, [a, b_]); return 1
        total += grouped(c, r, [t for t in NT if t != z1], 1, after4)
    return total

# ---------------------------------------------------------------- Thm 4.3
def two_resources():
    r, T, y, a, b_ = 0, [1, 2, 3, 4, 5], 'y', 'a', 'b'
    U = [r] + T
    total = 0
    for Na in subsets(T, 4):
        for Ny in subsets(T, 5):
            if len(Ny & Na) > 2: continue
            forced = [(r, t) for t in T] + [(r, y), (r, a), (r, b_), (a, b_)] + \
                     [(a, t) for t in Na] + [(y, t) for t in Ny]
            forb = [(y, a), (y, b_)] + [(a, t) for t in T if t not in Na] + [(y, t) for t in T if t not in Ny]
            adj = mkadj(forced, forb)
            held = [(r, t) for t in T] + [(r, y), (r, a), (r, b_), (a, b_)]
            b = {v: 1 for v in U + [y, a, b_]}; b[r] = 2; b[y] = 0
            c = Cert(U + [y, a, b_], b, held, adj)
            z1 = min(t for t in T if t not in Na)
            C = sorted(Ny & Na)
            c = c.single(r, b_, 0); c = c.single(b_, a, 0); c = c.single(r, z1, 0)
            P2 = C if len(C) == 2 else [t for t in T if t != z1]
            def after4(c4, z2):
                def after5(c5, z3):
                    Z = {z1, z2, z3}
                    S = [t for t in T if t not in Z]
                    S.sort(key=lambda s: -((s in Ny) + (s in Na)))
                    c6 = c5.single(S[0], r, 5); c7 = c6.single(S[1], r, 4)
                    c8 = c7.single(y, r, 3); c9 = c8.single(a, r, 2)
                    finish(c9, U, r, [y, a, b_]); return 1
                return grouped(c4, r, [t for t in T if t not in (z1, z2)], 2, after5)
            total += grouped(c, r, P2, 1, after4)
    return total

# ---------------------------------------------------------------- Thm 4.4
def relay(m):
    r, T = 0, [1, 2, 3, 4, 5]
    U = [r] + T
    cs = [f'c{i}' for i in range(1, m + 1)]; a = 'a'
    path = [r] + cs + [a]
    total = 0
    for N1 in subsets(T, 4):
        forced = [(r, t) for t in T] + list(zip(path, path[1:])) + [(cs[0], t) for t in N1]
        forb = [(cs[0], t) for t in T if t not in N1]
        forb += [(ci, u) for ci in cs[1:] for u in U] + [(a, u) for u in U] + [(a, ci) for ci in cs[:-1]]
        adj = mkadj(forced, forb)
        held = [(r, t) for t in T] + list(zip(path, path[1:]))
        b = {v: 1 for v in U + cs + [a]}; b[r] = 2; b[a] = 0
        c = Cert(U + cs + [a], b, held, adj)
        z1 = min(t for t in T if t not in N1)
        c = c.single(r, z1, 0)
        def after2(c2, z2):
            def after3(c3, z3):
                Z = {z1, z2, z3}
                S = [t for t in T if t not in Z]
                c4 = c3.single(S[0], r, 3); c5 = c4.single(S[1], r, 3)
                c6 = c5.single(cs[0], r, 2)             # relay start, bound 2
                for prev, nxt in zip(cs, cs[1:] + [a]):
                    c6 = c6.single(nxt, prev, 0)        # later receivers: no blank neighbour
                finish(c6, U, r, cs + [a]); return 1
            return grouped(c2, r, [t for t in T if t not in (z1, z2)], 2, after3)
        total += grouped(c, r, [t for t in T if t != z1], 1, after2)
    return total

# ---------------------------------------------------------------- Thm 5.2
def full_hub_two():
    U = [0, 1, 2, 3, 4, 5]; x, a1, b1, a2, b2 = 'x', 'a1', 'b1', 'a2', 'b2'
    bat = [(x, a1), (x, b1), (a1, b1), (x, a2), (x, b2), (a2, b2)]
    forced = [(x, u) for u in U] + bat
    forb = [(a, u) for a in (a1, a2) for u in U] + [(a1, b2)]
    adj = mkadj(forced, forb)
    sp = U + [x, a1, b1, a2, b2]
    total = 0
    for r in U:
        T = [u for u in U if u != r]
        b = {v: 1 for v in sp}
        c = Cert(sp, b, [(x, u) for u in U] + bat, adj)
        c = c.single(x, b1, 0); c = c.single(b1, a1, 0); c = c.single(x, b2, 0); c = c.single(b2, a2, 0)
        def rec(c, Z, j):
            if j == 3:
                S = [r] + [t for t in T if t not in Z]
                for s in S:
                    c = c.single(s, x, 3)
                c = c.single(a1, x, 1); c = c.single(a2, x, 0)
                if c.b[x] != 1: raise Fail("b(x)")
                finish(c, U, r, [x, a1, b1, a2, b2]); return 1
            return grouped(c, x, [t for t in T if t not in Z], j, lambda c2, z: rec(c2, Z | {z}, j + 1))
        total += rec(c, set(), 0)
    return total

def full_hub_pendant():
    U = [0, 1, 2, 3, 4, 5]; x, a1, b1, y = 'x', 'a1', 'b1', 'y'
    bat = [(x, a1), (x, b1), (a1, b1)]
    forced = [(x, u) for u in U] + bat + [(x, y)]
    forb = [(a1, u) for u in U] + [(y, u) for u in U] + [(y, b1)]
    adj = mkadj(forced, forb)
    sp = U + [x, a1, b1, y]
    total = 0
    for r in U:
        T = [u for u in U if u != r]
        b = {v: 1 for v in sp}; b[x] = 2; b[y] = 0
        c = Cert(sp, b, [(x, u) for u in U] + bat + [(x, y)], adj)
        c = c.single(x, b1, 0); c = c.single(b1, a1, 0)
        def rec(c, Z, j):
            if j == 3:
                for s in [r] + [t for t in T if t not in Z]:
                    c = c.single(s, x, 3)
                c = c.single(y, x, 1); c = c.single(a1, x, 0)
                if c.b[x] != 1: raise Fail("b(x)")
                finish(c, U, r, [x, a1, b1, y]); return 1
            return grouped(c, x, [t for t in T if t not in Z], j, lambda c2, z: rec(c2, Z | {z}, j + 1))
        total += rec(c, set(), 0)
    return total

# ---------------------------------------------------------------- Thm 6.1
def general_root(d, beta):
    U = list(range(d)); r = 0; T = U[1:]; y = 'y'
    bat = [(f'a{i}', f'b{i}') for i in range(beta)]
    tri = [e for a, b in bat for e in ((r, a), (r, b), (a, b))]
    forced = [(r, t) for t in T] + [(r, y)] + tri
    forb = [(y, t) for t in T] + [(a, t) for a, _ in bat for t in T] + [(b, y) for _, b in bat]
    forb += [(bat[i][0], bat[j][1]) for i in range(beta) for j in range(i + 1, beta)]
    adj = mkadj(forced, forb)
    sp = U + [y] + [v for p in bat for v in p]
    b = {v: 1 for v in sp}; b[r] = 2; b[y] = 0
    c = Cert(sp, b, [(r, t) for t in T] + [(r, y)] + tri, adj)
    for a, bb in bat:
        c = c.single(r, bb, 0); c = c.single(bb, a, 0)
    def rec(c, Z, j):
        if j == d // 2:
            for s in [t for t in T if t not in Z]:
                c = c.single(s, r, d // 2)
            pay = [y] + [a for a, _ in bat]
            for jj, v in enumerate(pay):
                c = c.single(v, r, beta - jj)
            finish(c, U, r, [y] + [v for p in bat for v in p], expect_doubled=d // 2); return 1
        return grouped(c, r, [t for t in T if t not in Z], j, lambda c2, z: rec(c2, Z | {z}, j + 1))
    return rec(c, frozenset(), 0)

def general_full(d, beta, pendant):
    U = list(range(d)); x = 'x'; y = 'y'
    bat = [(f'a{i}', f'b{i}') for i in range(beta)]
    tri = [e for a, b in bat for e in ((x, a), (x, b), (a, b))]
    forced = [(x, u) for u in U] + tri + ([(x, y)] if pendant else [])
    forb = [(a, u) for a, _ in bat for u in U]
    forb += [(bat[i][0], bat[j][1]) for i in range(beta) for j in range(i + 1, beta)]
    if pendant:
        forb += [(y, u) for u in U] + [(b, y) for _, b in bat]
    adj = mkadj(forced, forb)
    sp = U + [x] + [v for p in bat for v in p] + ([y] if pendant else [])
    total = 0
    for r in U:
        T = [u for u in U if u != r]
        b = {v: 1 for v in sp}
        if pendant: b[x] = 2; b[y] = 0
        c = Cert(sp, b, [(x, u) for u in U] + tri + ([(x, y)] if pendant else []), adj)
        for a, bb in bat:
            c = c.single(x, bb, 0); c = c.single(bb, a, 0)
        def rec(c, Z, j):
            if j == d // 2:
                for s in [r] + [t for t in T if t not in Z]:
                    c = c.single(s, x, d // 2)
                pay = ([y] if pendant else []) + [a for a, _ in bat]
                for jj, v in enumerate(pay):
                    c = c.single(v, x, len(pay) - 1 - jj)
                if c.b[x] != 1: raise Fail("b(x)")
                finish(c, U, r, [x] + [v for p in bat for v in p] + ([y] if pendant else []),
                       expect_doubled=d // 2); return 1
            return grouped(c, x, [t for t in T if t not in Z], j, lambda c2, z: rec(c2, Z | {z}, j + 1))
        total += rec(c, frozenset(), 0)
    return total

def run(name, f, *args):
    try:
        n = f(*args)
        print(f"{name}: OK, {n} adversarial branches, every Fan inequality and every printed bound holds")
        return True
    except Fail as e:
        print(f"{name}: FAIL: {e}")
        return False

if __name__ == '__main__':
    run("Thm 4.1(i)", roothub_i)
    run("Thm 4.1(ii)", roothub_ii)
    run("Thm 4.1(iii)", roothub_iii)
    run("Thm 4.3", two_resources)
    for m in (1, 2, 3, 4):
        run(f"Thm 4.4, m = {m}", relay, m)
    run("Thm 5.2, two batteries", full_hub_two)
    run("Thm 5.2, battery + pendant", full_hub_pendant)
    for d in (4, 6, 8, 10):
        beta = max(0, d // 2 - 3)
        run(f"Thm 6.1(a), d = {d}, beta = {beta}", general_root, d, beta)
        run(f"Thm 6.1(b), d = {d}, beta = {d // 2 - 1}", general_full, d, d // 2 - 1, False)
        run(f"Thm 6.1(b) pendant, d = {d}, beta = {d // 2 - 2}", general_full, d, d // 2 - 2, True)
    print("-- sharpness of the battery counts in this model (expected to FAIL):")
    for d in (8, 10):
        run(f"Thm 6.1(a), d = {d}, beta = {d // 2 - 4}", general_root, d, d // 2 - 4)
        run(f"Thm 6.1(b), d = {d}, beta = {d // 2 - 2}", general_full, d, d // 2 - 2, False)

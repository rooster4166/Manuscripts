"""A38: independent check of the three converses of the overview paper and of Lemmas 3.1, 3.2.

(A) Prop 3.11 (all-odd (T1) lift): J with z its only even vertex, |J| = 2k+1, B = J - z,
    Phi a forest N(z)-join of B, ANY rooting.
      LHS: H = B - Phi has a Lovasz decomposition with (i), (ii);
      RHS: B has a decomposition into <= k paths with Phi terminal at parents.
    Also: no RHS decomposition has fewer than c(u) ends at any u in N(z) (and parity is even).
(B) Prop 3.15 ((T2) forest lift): z, r the only even vertices of J, adjacent, |J| = n even,
    d_J(r) >= 3; L = J - {zv : v in N(z) - r}; Phi a forest N(z)-join of J - z; ANY rooting.
      LHS: M = L - Phi has a Lovasz decomposition with (i), (ii);
      RHS: L has a decomposition into <= n/2 paths with Phi terminal at parents.
    Also: for admissible rootings (r a root, or a child with c(r) >= 2) no RHS decomposition has
    fewer than 2 ends at r; the Lemma 3.13 step then gives (T2), which is executed and checked.
(C) Prop 3.17 (floor lift): B of odd order whose even-degree vertices (degree 0 included) are
    w and T; Phi a forest T-join, rooted with w never a child.
      LHS: B - Phi has a Lovasz decomposition with (i), (ii);
      RHS: B has a decomposition into <= (|B|-1)/2 paths with Phi terminal at parents.
Every LHS witness is lifted (Lemma 3.1) and checked; every RHS witness is stripped (Lemma 3.2)
and checked.  On the smaller instances the RHS is also decided by full enumeration (cross-check
of the search).  usage: python3 conv.py MODE FILE.g6 [maxedges] [fullenum]
  MODE A: FILE lists J (one even vertex);  B: J (two adjacent even vertices);  C: graphs B.
"""
import sys
from collections import Counter
from a38lib import (G, graph6, forest_tjoins, rootings, children_count, find_base, find_decomp,
                    append_forest, strip, is_path_decomp, is_parity_decomp, terminal_at_parents,
                    ends, norm, decomps, base_ok)


def terminal_ok_factory(phi, par):
    """path_ok for 'Phi terminal at parents': every Phi-edge on P is an end edge of P, at the
    parent's end."""
    pe = {}
    for v, p in par.items():
        pe[norm(v, p)] = p

    def ok(P):
        for i in range(len(P) - 1):
            e = norm(P[i], P[i + 1])
            if e in pe:
                p = pe[e]
                if not ((i == 0 and P[0] == p) or (i == len(P) - 2 and P[-1] == p)):
                    return False
        return True
    return ok


BIG = 10 ** 6


def rhs_search(g, maxp, phi, par, cap=None):
    if cap is None:
        cap = [BIG] * g.n
    return find_decomp(g, maxp, cap, terminal_ok_factory(phi, par))


def check_strip(g, D, phi, par, stats):
    """Lemma 3.2 on a decomposition D of g in which phi is terminal at parents."""
    assert terminal_at_parents(D, par)
    Dm = strip(D, phi)
    gm = g.minus(list(phi))
    assert is_path_decomp(gm, Dm), "stripped family is not a decomposition"
    assert len(Dm) <= len(D)
    if len(Dm) == len(D):
        for v, p in par.items():
            # the shortened path of the path containing p(v)v ends at v and avoids p(v)
            e = norm(v, p)
            idx = [i for i, P in enumerate(D) if any(norm(P[j], P[j + 1]) == e
                                                     for j in range(len(P) - 1))]
            assert len(idx) == 1
            Pm = strip([D[idx[0]]], phi)
            assert len(Pm) == 1
            Pm = Pm[0]
            assert v in (Pm[0], Pm[-1]) and p not in Pm, "Lemma 3.2 end claim fails"
        stats["strip_equal"] += 1
    return Dm


def instance(g, K, maxp, phi, par, stats, fullenum_list=None, extra=None):
    """g: the graph with phi (B or L); K = g - phi; maxp: budget.  Returns (lhs, rhs)."""
    D0 = find_base(K, par)
    lhs = D0 is not None
    if lhs:
        Lf = append_forest(D0, par)
        assert is_path_decomp(g, Lf) and len(Lf) == len(D0) <= maxp
        assert terminal_at_parents(Lf, par)
        c = children_count(par)
        b0, b1 = ends(D0, g.n), ends(Lf, g.n)
        for u in range(g.n):
            assert b1[u] == b0[u] - (u in par) + c[u], "end formula of Lemma 3.1"
        stats["lifts"] += 1
    D1 = rhs_search(g, maxp, phi, par)
    rhs = D1 is not None
    if rhs:
        Dm = check_strip(g, D1, phi, par, stats)
    if fullenum_list is not None:
        rhs2 = any(terminal_at_parents(D, par) for D in fullenum_list)
        assert rhs2 == rhs, "search and enumeration disagree on RHS"
        for D in fullenum_list:
            if terminal_at_parents(D, par):
                check_strip(g, D, phi, par, stats)
                if extra is not None:
                    extra(D)
        stats["fullenum"] += 1
    return lhs, rhs


def modeA(J, stats, fullenum):
    z = [v for v in range(J.n) if J.deg(v) % 2 == 0]
    if len(z) != 1 or J.n % 2 == 0:
        return
    z = z[0]
    Nz = J.adj[z]
    if not Nz:
        return
    k = (J.n - 1) // 2
    B = J.delvert(z)
    allD = list(decomps(B, k)) if fullenum else None
    for phi in forest_tjoins(B, Nz):
        H = B.minus(list(phi))
        for par in rootings(J.n, phi):
            c = children_count(par)

            def extra(D):
                b = ends(D, J.n)
                for u in Nz:
                    assert b[u] % 2 == 0 and b[u] >= c[u], "Prop 3.11 end claim"
            lhs, rhs = instance(B, H, k, phi, par, stats, allD, extra)
            # end claim by search: a RHS decomposition with fewer than c(u) ends at some u in N(z)
            if rhs and not fullenum:
                for u in Nz:
                    if c[u] >= 1:
                        cap = [BIG] * J.n
                        cap[u] = c[u] - 1
                        assert rhs_search(B, k, phi, par, cap) is None, "Prop 3.11 end claim"
            stats["A_inst"] += 1
            stats["A_agree"] += int(lhs == rhs)
            stats["A_pos"] += int(lhs)
            if lhs != rhs:
                print("A DISAGREE", J.edges, z, phi, par, lhs, rhs, flush=True)
            # Theorem 3.10 cases (a), (b): (T1) at every r in N(z) that is a root or a child
            # with >= 2 children, whenever the base exists (lift checked in instance()).


def modeB(J, stats, fullenum):
    ev = [v for v in range(J.n) if J.deg(v) % 2 == 0]
    if len(ev) != 2 or J.n % 2 == 1:
        return
    a, b = ev
    if norm(a, b) not in J.eidx:
        return
    for z, r in ((a, b), (b, a)):
        if J.deg(r) < 3:
            continue
        n = J.n
        Nz = J.adj[z]
        T = [v for v in Nz if v != r]
        Lg = J.minus([(z, v) for v in T])
        Bz = J.delvert(z)
        allD = list(decomps(Lg, n // 2)) if fullenum else None
        for phi in forest_tjoins(Bz, Nz):
            M = Lg.minus(list(phi))
            for par in rootings(n, phi):
                c = children_count(par)
                adm = (r not in par) or c[r] >= 2

                def extra(D):
                    if adm:
                        assert ends(D, n)[r] >= 2, "Prop 3.15 end claim"
                lhs, rhs = instance(Lg, M, n // 2, phi, par, stats, allD, extra)
                if rhs and adm and not fullenum:
                    cap = [BIG] * n
                    cap[r] = 1
                    assert rhs_search(Lg, n // 2, phi, par, cap) is None, "Prop 3.15 end claim"
                if rhs and adm:
                    # Lemma 3.13: trim z / drop zr and split, giving (T2)
                    D1 = rhs_search(Lg, n // 2, phi, par)
                    out = []
                    for P in D1:
                        if z in P:
                            P = P[1:] if P[0] == z else P[:-1]
                            if len(P) >= 2:
                                out.append(tuple(P))
                        else:
                            out.append(P)
                    br = sum((P[0] == r) + (P[-1] == r) for P in out)
                    if br < 3:
                        for i, P in enumerate(out):
                            if r in P[1:-1]:
                                j = P.index(r)
                                out = out[:i] + [P[:j + 1], P[j:]] + out[i + 1:]
                                break
                    assert is_path_decomp(Bz, out) and len(out) <= n // 2
                    assert ends(out, n)[r] >= 3, "(T2) via Lemma 3.13"
                    stats["B_T2"] += 1
                stats["B_inst"] += 1
                stats["B_adm"] += int(adm)
                stats["B_agree"] += int(lhs == rhs)
                stats["B_pos"] += int(lhs)
                if lhs != rhs:
                    print("B DISAGREE", J.edges, z, r, phi, par, lhs, rhs, flush=True)


def modeC(Bg, stats, fullenum):
    if Bg.n % 2 == 0:
        return
    E = [v for v in range(Bg.n) if Bg.deg(v) % 2 == 0]
    maxp = (Bg.n - 1) // 2
    allD = list(decomps(Bg, maxp)) if fullenum else None
    for w in E:
        T = [v for v in E if v != w]
        for phi in forest_tjoins(Bg, T):
            K = Bg.minus(list(phi))
            for par in rootings(Bg.n, phi):
                if w in par:
                    continue
                lhs, rhs = instance(Bg, K, maxp, phi, par, stats, allD)
                stats["C_inst"] += 1
                stats["C_agree"] += int(lhs == rhs)
                stats["C_pos"] += int(lhs)
                if lhs != rhs:
                    print("C DISAGREE", Bg.edges, w, phi, par, lhs, rhs, flush=True)


def main():
    mode, path = sys.argv[1], sys.argv[2]
    maxe = int(sys.argv[3]) if len(sys.argv) > 3 else 99
    fullenum = len(sys.argv) > 4 and sys.argv[4] == "1"
    stats = Counter()
    ng = 0
    for line in open(path):
        s = line.strip()
        if not s:
            continue
        g = graph6(s)
        if g.m() > maxe:
            continue
        if mode == "C":
            # also the graph plus an isolated vertex when that keeps the order odd
            gs = [g] if g.n % 2 == 1 else [G(g.n + 1, g.edges)]
        else:
            gs = [g]
        for h in gs:
            ng += 1
            {"A": modeA, "B": modeB, "C": modeC}[mode](h, stats, fullenum)
    print("mode", mode, "file", path.split("/")[-1], "graphs", ng, dict(sorted(stats.items())))


if __name__ == "__main__":
    main()

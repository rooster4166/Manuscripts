"""A38: exact base analysis at every root of a (J, z), independent of the overview scripts.

For J with z its only even vertex (order 2k+1), at each r in N(z) it decides exactly:
  data   : triangle data exist (a perfect matching of N(z)-{r,w} by edges of J, some w);
  tri    : a triangle base exists (overview Thm 3.4 / Def 3.3);
  forest : a forest base exists (overview Thm 3.7): w in N(z)-r, T = N(z)-{r,w},
           Phi a forest T-join of J-{z,r}, every rooting with w never a child;
  thru_r : the synthesis S25 variant: Phi a forest T-join of J-z (r allowed in Phi), r a root
           (r is not in T, so d_Phi(r) is even), w never a child;
  ao_a   : all-odd base, case (a): Phi a forest N(z)-join of B = J-z, r a root;
  ao_b   : all-odd base, case (b): r a child with c(r) >= 2;
  t1     : (T1) at r (a decomposition of B into <= k paths with >= 2 ends at r).
Every base found is lifted (Lemma 3.1, plus the leaf step for the lifts that keep z) and the
lift is verified.  Usage: python3 roots_bases.py G6 [G6 ...]   (or 'K26' for the cone over K_{2,6}).
"""
import sys
import itertools
from a38lib import (G, decomps, ends, is_path_decomp, is_parity_decomp, forest_tjoins,
                    rootings, children_count, base_ok, append_forest, graph6, connectivity, norm)


def cone_k26():
    es = [(h, y) for h in (0, 1) for y in range(2, 8)] + [(8, v) for v in range(8)]
    return G(9, es), 8


def lovasz_decomps(g):
    odd = len(g.odd())
    return [D for D in decomps(g, odd // 2) if is_parity_decomp(g, D)]


def t1_holds(B, k, r):
    for D in decomps(B, k):
        if ends(D, B.n)[r] >= 2:
            return True
    return False


def leaf_step(D, z, r, Bdeg_r):
    """Delete the leaf z (attached at r) from a decomposition of B+leaf: trim z, or drop zr and
    split a path through r.  Returns a decomposition of B (list of paths)."""
    out = []
    dropped = False
    for P in D:
        if z in P:
            P = list(P)
            if P[0] == z:
                P = P[1:]
            else:
                P = P[:-1]
            if len(P) >= 2:
                out.append(tuple(P))
            else:
                dropped = True
        else:
            out.append(P)
    b = ends(out, max(max(P) for P in out) + 1 if out else 0)
    if b[r] if r < len(b) else 0:
        pass
    # if r ends fewer than 2 paths, split a path through r
    br = sum((P[0] == r) + (P[-1] == r) for P in out)
    if br < 2:
        for i, P in enumerate(out):
            if r in P[1:-1]:
                j = P.index(r)
                out = out[:i] + [P[:j + 1], P[j:]] + out[i + 1:]
                break
    return out


def analyze(J, z, want=("data", "tri", "forest", "thru_r", "ao_a", "ao_b", "t1")):
    n = J.n
    assert all((J.deg(v) % 2 == 0) == (v == z) for v in range(n)), "z must be the only even vertex"
    k = (n - 1) // 2
    Nz = J.adj[z]
    m = len(Nz) // 2
    B = J.delvert(z)
    res = {}
    lov_cache = {}

    def lov(g):
        key = tuple(g.edges)
        if key not in lov_cache:
            lov_cache[key] = lovasz_decomps(g)
        return lov_cache[key]

    for r in Nz:
        out = {}
        others = [v for v in Nz if v != r]
        # ---- triangle data and base
        datas = []
        for w in others:
            T = [v for v in others if v != w]

            def pms(rest):
                if not rest:
                    yield []
                    return
                a = rest[0]
                for b in rest[1:]:
                    if norm(a, b) in J.eidx:
                        for pm in pms([x for x in rest[1:] if x != b]):
                            yield [(a, b)] + pm
            for pm in pms(T):
                datas.append((w, pm))
        out["data"] = bool(datas)
        tri = False
        for (w, pm) in datas:
            rem = [(z, w)] + [(z, a) for a, b in pm] + [(z, b) for a, b in pm] + pm
            M = J.minus(rem)
            for D in lov(M):
                # disjunction for every pair
                okd = True
                for a, b in pm:
                    qa = [P for P in D if a in (P[0], P[-1])]
                    qb = [P for P in D if b in (P[0], P[-1])]
                    if not (a not in qb[0] or b not in qa[0]):
                        okd = False
                        break
                if okd:
                    tri = True
                    break
            if tri:
                break
        out["tri"] = tri
        # ---- forest base (Thm 3.7) and the variant through r
        for key, through in (("forest", False), ("thru_r", True)):
            if key not in want:
                continue
            found = False
            for w in others:
                T = [v for v in others if v != w]
                H = J.delvert(z) if through else J.delvert(z).delvert(r)
                for phi in forest_tjoins(H, T):
                    M = J.minus([(z, w)] + [(z, v) for v in T] + list(phi))
                    Ds = None
                    for par in rootings(n, phi):
                        if w in par:
                            continue
                        if through and r in par:
                            continue
                        if Ds is None:
                            Ds = lov(M)
                        for D in Ds:
                            if base_ok(D, par):
                                # lift: append forest in J - zw - zT (= B + leaf z at r), then leaf step
                                L = append_forest(D, par)
                                Lg = J.minus([(z, w)] + [(z, v) for v in T])
                                assert is_path_decomp(Lg, L), ("lift not a decomposition", key, r)
                                D1 = leaf_step(L, z, r, B.deg(r))
                                assert is_path_decomp(B, D1) and len(D1) <= k, ("leaf step", key)
                                assert ends(D1, n)[r] >= 2, ("ends at r", key)
                                found = True
                                break
                        if found:
                            break
                    if found:
                        break
                if found:
                    break
            out[key] = found
        # ---- all-odd lift
        for key in ("ao_a", "ao_b"):
            found = False
            nphi = 0
            nroot = 0
            for phi in forest_tjoins(B, Nz):
                nphi += 1
                H = B.minus(list(phi))
                Ds = None
                for par in rootings(n, phi):
                    c = children_count(par)
                    if key == "ao_a" and r in par:
                        continue
                    if key == "ao_b" and not (r in par and c[r] >= 2):
                        continue
                    nroot += 1
                    if Ds is None:
                        Ds = lov(H)
                    for D in Ds:
                        if base_ok(D, par):
                            L = append_forest(D, par)
                            assert is_path_decomp(B, L) and len(L) == k
                            br = ends(L, n)[r]
                            assert br == 1 - (r in par) + c[r] and br >= 2
                            found = True
                            break
                    if found and "count" not in want:
                        break
                if found and "count" not in want:
                    break
            out[key] = found
            out[key + "_forests"] = nphi
            out[key + "_rootings"] = nroot
        if "t1" in want:
            out["t1"] = t1_holds(B, k, r)
        res[r] = out
    return res


def main(args):
    for s in args:
        if s == "K26":
            J, z = cone_k26()
        else:
            J = graph6(s)
            z = [v for v in range(J.n) if J.deg(v) % 2 == 0]
            assert len(z) == 1, "not exactly one even vertex"
            z = z[0]
        nz = J.adj[z]
        indep = all(norm(a, b) not in J.eidx for a, b in itertools.combinations(nz, 2))
        print(f"{s}: n={J.n} m={J.m()} z={z} d(z)={J.deg(z)} N(z)={nz} independent={indep} "
              f"kappa={connectivity(J)}")
        res = analyze(J, z, want=("data", "tri", "forest", "thru_r", "ao_a", "ao_b", "t1", "count"))
        for r, o in res.items():
            print(f"  r={r} d_J(r)={J.deg(r)} " + " ".join(f"{k}={v}" for k, v in o.items()))


if __name__ == "__main__":
    main(sys.argv[1:] or ["K26", "HsaAD~}"])

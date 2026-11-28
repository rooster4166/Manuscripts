"""A38: every root WITHOUT triangle data of every 3-connected J of order 9 with exactly one even
vertex.  For each such root decide, exactly, whether a forest base (overview Thm 3.7) exists,
and if not, whether an all-odd base exists in case (a) or (b) (Thm 3.10).  Every base found is
lifted and the lift is checked as a (T1) decomposition.  Independent of the overview scripts and
of direct-test1/scripts/fb_nodata.py.

usage: python3 nodata9.py LIST.g6 [procs]
"""
import sys
from multiprocessing import Pool
from collections import Counter
from a38lib import (G, graph6, forest_tjoins, rootings, children_count, find_base, append_forest,
                    is_path_decomp, ends, norm)


def has_pm(J, verts):
    verts = list(verts)
    if not verts:
        return True
    a = verts[0]
    for b in verts[1:]:
        if norm(a, b) in J.eidx and has_pm(J, [x for x in verts[1:] if x != b]):
            return True
    return False


def leaf_step(D, z, r):
    out = []
    for P in D:
        if z in P:
            P = list(P)
            P = P[1:] if P[0] == z else P[:-1]
            if len(P) >= 2:
                out.append(tuple(P))
        else:
            out.append(P)
    br = sum((P[0] == r) + (P[-1] == r) for P in out)
    if br < 2:
        for i, P in enumerate(out):
            if r in P[1:-1]:
                j = P.index(r)
                out = out[:i] + [P[:j + 1], P[j:]] + out[i + 1:]
                break
    return out


def forest_base(J, z, r):
    n = J.n
    k = (n - 1) // 2
    B = J.delvert(z)
    others = [v for v in J.adj[z] if v != r]
    for w in others:
        T = [v for v in others if v != w]
        H = B.delvert(r)
        for phi in forest_tjoins(H, T):
            M = J.minus([(z, w)] + [(z, v) for v in T] + list(phi))
            for par in rootings(n, phi):
                if w in par:
                    continue
                D = find_base(M, par)
                if D is not None:
                    L = append_forest(D, par)
                    Lg = J.minus([(z, w)] + [(z, v) for v in T])
                    assert is_path_decomp(Lg, L)
                    D1 = leaf_step(L, z, r)
                    assert is_path_decomp(B, D1) and len(D1) <= k and ends(D1, n)[r] >= 2
                    return True
    return False


def allodd_base(J, z, r, case):
    n = J.n
    k = (n - 1) // 2
    B = J.delvert(z)
    for phi in forest_tjoins(B, J.adj[z]):
        H = B.minus(list(phi))
        for par in rootings(n, phi):
            c = children_count(par)
            if case == "a" and r in par:
                continue
            if case == "b" and not (r in par and c[r] >= 2):
                continue
            D = find_base(H, par)
            if D is not None:
                L = append_forest(D, par)
                assert is_path_decomp(B, L) and len(L) == k and ends(L, n)[r] >= 2
                return True
    return False


def work(s):
    J = graph6(s)
    z = [v for v in range(J.n) if J.deg(v) % 2 == 0][0]
    Nz = J.adj[z]
    out = []
    for r in Nz:
        rest = [v for v in Nz if v != r]
        if any(has_pm(J, [v for v in rest if v != w]) for w in rest):
            continue
        f = forest_base(J, z, r)
        a = b = None
        if not f:
            a = allodd_base(J, z, r, "a")
            b = allodd_base(J, z, r, "b")
        out.append((s, r, J.deg(z), f, a, b))
    return out


def main(path, procs=4):
    graphs = [l.strip() for l in open(path) if l.strip()]
    cnt = Counter()
    with Pool(procs) as pool:
        for res in pool.imap_unordered(work, graphs, chunksize=8):
            for (s, r, dz, f, a, b) in res:
                cnt["nodata_roots"] += 1
                cnt[("nodata_roots", dz)] += 1
                if f:
                    cnt["forest"] += 1
                else:
                    cnt["no_forest"] += 1
                    print("NO FOREST BASE:", s, "r =", r, "d(z) =", dz, "all-odd (a):", a,
                          "(b):", b, flush=True)
                    if a or b:
                        cnt["allodd"] += 1
                    else:
                        cnt["uncovered"] += 1
    for kk in sorted(cnt, key=str):
        print(kk, cnt[kk])


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 4)

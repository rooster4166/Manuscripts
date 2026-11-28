"""A38: the four order-10 (T2) instances of test2/data/forestbase2_order10_nonroot.txt.
Exact: is there a (T2) forest base (overview Thm 3.14) with r a root?  with r a child, c(r) >= 2?
Every base found is lifted (Lemma 3.1 in the leaf graph L, then Lemma 3.13) and checked."""
from a38lib import graph6, forest_tjoins, rootings, children_count, find_base, append_forest, \
    is_path_decomp, ends

INST = [("I???F~}~o", 7, 9), ("I???F~}~o", 9, 7), ("I??CFx~~w", 7, 8), ("I??CFx~~w", 8, 7)]


def run(s, z, r):
    J = graph6(s)
    n = J.n
    Nz = J.adj[z]
    T = [v for v in Nz if v != r]
    L = J.minus([(z, v) for v in T])
    B = J.delvert(z)
    res = {"root": False, "child": False}
    nphi = 0
    for phi in forest_tjoins(B, Nz):
        nphi += 1
        M = L.minus(list(phi))
        assert all(M.deg(v) % 2 == 1 for v in range(n))
        for par in rootings(n, phi):
            c = children_count(par)
            kind = "root" if r not in par else ("child" if c[r] >= 2 else None)
            if kind is None or res[kind]:
                continue
            D = find_base(M, par)
            if D is not None:
                Lf = append_forest(D, par)
                assert is_path_decomp(L, Lf) and len(Lf) <= n // 2 and ends(Lf, n)[r] >= 2
                res[kind] = True
    return nphi, res


for s, z, r in INST:
    print(s, "z =", z, "r =", r, *run(s, z, r))

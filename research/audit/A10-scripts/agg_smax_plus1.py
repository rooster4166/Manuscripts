# MUTANT of indep_aggregate.py: smax = (k-4)//2 + 1 (one more S colour than Thm B allows).
"""Independent check (A10 referee) of the aggregation in Props UH and LH of jm-repair.tex.

Relaxation: a colour is a per-colour profile (type, p, n0, n1, n2) with n0+n1+n2 = p,
1 <= p <= k (type T) or p <= k-1 (types c, S).  The only global facts kept are
  UH:  sum_i f_i(B) = k b   (b integer)      ->  sum f_B == 0 (mod k)
  LH:  sum_i f_i(A) = k a   (a integer)      ->  sum f_A == 0 (mod k)
together with: exactly one colour of type c, any number of type T, and at most
floor((k-4)/2) colours of type S (LH only; UH does not use the |U| bound, and S is a
sub-case of T there).  (UH) fails for some configuration iff min sum u_i < 0;
(LH) fails iff min sum s_i < 0, where u_i, s_i are as in the manuscript.
Min-plus closure over residues mod k (exact, not sampled)."""
import sys
import numpy as np
INF = 10 ** 9

def prof(k, typ):
    pmax = k if typ == "T" else k - 1
    eps = {"T": 4, "c": 3, "S": 5}[typ]; kap = 2 if typ == "c" else 4
    for p in range(1, pmax + 1):
        delta = max(0, p + eps - k)
        for n0 in range(p + 1):
            for n1 in range(p - n0 + 1):
                n2 = p - n0 - n1
                fA, fB = 2 * n0 + n1, n1 + 2 * n2
                psi = n1 + n2 + (1 if (n2 >= 1 and typ != "c") else 0)
                D = max(0, delta - psi)
                yield fA, fB, 2 * fA - k * D, k * min(kap, psi) - 2 * fB

def best_by_residue(k, typ, which):
    b = np.full(k, INF, dtype=np.int64)
    for fA, fB, s, u in prof(k, typ):
        r, w = (fB % k, u) if which == "UH" else (fA % k, s)
        if w < b[r]: b[r] = w
    return b

def minplus(a, b, k):
    # c[r] = min_j a[j] + b[(r - j) mod k]
    idx = (np.arange(k)[:, None] - np.arange(k)[None, :]) % k   # idx[r, j] = r - j
    return np.min(a[None, :] + b[idx], axis=1)

def closure(b, k):
    """D[r] = min weight of a multiset (possibly empty) of items with residue sum r; weights >= 0."""
    assert (b[b < INF] >= 0).all()
    D = np.full(k, INF, dtype=np.int64); D[0] = 0
    while True:
        nd = np.minimum(D, minplus(D, b, k)); nd = np.minimum(nd, INF)
        if (nd == D).all(): return D
        D = nd

def check(k):
    # UH
    nonc = np.minimum(best_by_residue(k, "T", "UH"), best_by_residue(k, "S", "UH"))
    Dn = closure(nonc, k)
    cU = best_by_residue(k, "c", "UH")
    uh_min = int(np.min(cU + Dn[(-np.arange(k)) % k]))
    # LH
    smax = (k - 4) // 2 + 1
    DT = closure(best_by_residue(k, "T", "LH"), k)
    cL = best_by_residue(k, "c", "LH"); SL = best_by_residue(k, "S", "LH")
    cur = np.minimum(minplus(DT, cL, k), INF)
    lh_min = int(cur[0])
    for j in range(smax):
        cur = np.minimum(minplus(cur, SL, k), INF)
        lh_min = min(lh_min, int(cur[0]))
    return uh_min, lh_min

if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    smax_override = None
    bad = []
    for k in range(4, kmax + 1):
        uh, lh = check(k)
        if uh < 0 or lh < 0: bad.append((k, uh, lh))
        if k <= 12 or k % 10 == 0: print(k, "min sum u =", uh, " min sum s =", lh, flush=True)
    print("k range 4..%d: failures" % kmax, bad)

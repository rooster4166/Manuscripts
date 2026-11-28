"""A38: triangle bases at every root WITH data of every 3-connected J of order 9 with exactly one
even vertex (exact: every data choice and orientation until one works).  Each base is lifted
through Lemma 3.1 with one-edge components plus the leaf step, and the lift is checked.
usage: python3 tri9.py LIST.g6 [procs]"""
import sys
import itertools
from multiprocessing import Pool
from collections import Counter
from a38lib import G, graph6, find_decomp, append_forest, is_path_decomp, ends, norm
from nodata9 import leaf_step


def pms(J, rest):
    if not rest:
        yield []
        return
    a = rest[0]
    for b in rest[1:]:
        if norm(a, b) in J.eidx:
            for pm in pms(J, [x for x in rest[1:] if x != b]):
                yield [(a, b)] + pm


def tri_base(J, z, r):
    n = J.n
    k = (n - 1) // 2
    B = J.delvert(z)
    others = [v for v in J.adj[z] if v != r]
    anydata = False
    for w in others:
        T = [v for v in others if v != w]
        for pm in pms(J, T):
            anydata = True
            M = J.minus([(z, w)] + [(z, v) for v in T] + pm)
            cap = [M.deg(v) % 2 for v in range(n)]
            for orient in itertools.product((0, 1), repeat=len(pm)):
                par = {}
                for (a, b), o in zip(pm, orient):
                    y, x = (b, a) if o == 0 else (a, b)   # path ending at y avoids x
                    par[y] = x

                def ok(P):
                    for e in (P[0], P[-1]):
                        if e in par and par[e] in P:
                            return False
                    return True
                D = find_decomp(M, sum(cap) // 2, cap, ok)
                if D is not None:
                    # appending x y at y is Lemma 3.1 with one-edge components rooted at x
                    L = append_forest(D, par)
                    Lg = J.minus([(z, w)] + [(z, v) for v in T])
                    assert is_path_decomp(Lg, L)
                    D1 = leaf_step(L, z, r)
                    assert is_path_decomp(B, D1) and len(D1) <= k and ends(D1, n)[r] >= 2
                    return True
    return None if not anydata else False


def work(s):
    J = graph6(s)
    z = [v for v in range(J.n) if J.deg(v) % 2 == 0][0]
    out = []
    for r in J.adj[z]:
        t = tri_base(J, z, r)
        if t is not None:
            out.append((s, r, J.deg(z), t))
    return out


def main(path, procs=4):
    graphs = [l.strip() for l in open(path) if l.strip()]
    cnt = Counter()
    with Pool(procs) as pool:
        for res in pool.imap_unordered(work, graphs, chunksize=8):
            for (s, r, dz, t) in res:
                cnt[("data_roots", dz)] += 1
                cnt[("base", dz)] += int(t)
                if not t:
                    print("NO TRIANGLE BASE:", s, r, dz, flush=True)
    for kk in sorted(cnt, key=str):
        print(kk, cnt[kk])


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 4)

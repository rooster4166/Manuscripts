"""A38: the all-odd lift (overview Thm 3.10, case (a)) in its matching form at every root of every
3-connected J of order 9 with exactly one even vertex and a perfect matching of J[N(z)]:
Phi a perfect matching of J[N(z)] by edges of B = J - z, r a root (r matched to a0, the edge
oriented a0 -> r), every orientation of the other pairs.  Exact (find_base).  Each base is lifted
and the lift checked as a (T1) decomposition.  usage: python3 allodd9.py LIST.g6 [procs] [dz]"""
import sys
import itertools
from multiprocessing import Pool
from collections import Counter
from a38lib import graph6, find_base, append_forest, is_path_decomp, ends
from tri9 import pms


def work(args):
    s, dzwant = args
    J = graph6(s)
    z = [v for v in range(J.n) if J.deg(v) % 2 == 0][0]
    if dzwant and J.deg(z) != dzwant:
        return []
    Nz = J.adj[z]
    B = J.delvert(z)
    k = (J.n - 1) // 2
    allpm = list(pms(J, list(Nz)))
    if not allpm:
        return []
    out = []
    for r in Nz:
        found = False
        for pm in allpm:
            H = B.minus(pm)
            rest = [p for p in pm if r not in p]
            a0 = [p for p in pm if r in p][0]
            a0 = a0[0] if a0[1] == r else a0[1]
            for orient in itertools.product((0, 1), repeat=len(rest)):
                par = {a0: r}
                for (a, b), o in zip(rest, orient):
                    if o == 0:
                        par[b] = a
                    else:
                        par[a] = b
                D = find_base(H, par)
                if D is not None:
                    L = append_forest(D, par)
                    assert is_path_decomp(B, L) and len(L) == k and ends(L, J.n)[r] >= 2
                    found = True
                    break
            if found:
                break
        out.append((s, r, J.deg(z), J.deg(r), found))
    return out


def main(path, procs=2, dz=0):
    graphs = [(l.strip(), dz) for l in open(path) if l.strip()]
    cnt = Counter()
    with Pool(procs) as pool:
        for res in pool.imap_unordered(work, graphs, chunksize=8):
            for (s, r, dzz, dr, f) in res:
                cnt[("roots", dzz)] += 1
                cnt[("base", dzz)] += int(f)
                cnt[("roots_deg", dzz, dr)] += 1
                cnt[("base_deg", dzz, dr)] += int(f)
                if not f:
                    print("NO ALL-ODD MATCHING BASE:", s, r, dzz, dr, flush=True)
    for kk in sorted(cnt, key=str):
        print(kk, cnt[kk])


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 2,
         int(sys.argv[3]) if len(sys.argv) > 3 else 0)

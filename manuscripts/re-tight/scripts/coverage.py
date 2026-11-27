"""coverage.py N RETL_FILE [OUT]: coverage of the degree-(n-2) roots of the 2-connected Eulerian graphs
of order N by the sufficient conditions of the manuscript, by the literature, and by the Lovasz
method (ret.c -L output RETL_FILE).

Per root r (d(r) = n - 2, s the non-neighbour, k = n/2, h_t = #{x in N(r): d(x) >= 2t}):
  star     condition (*) (Corollary 3.4(c)): floor(h_t / 2) <= k + 1 - t for 3 <= t <= k - 1
  star2    condition (**) of Theorem 3.1: for 3 <= t <= k - 1, floor(h_t / 2) <= k + 1 - t or
           floor(h_{t+1} / 2) <= k + 1 - 2t
  cor168   at least k vertices of degree n - 2 (marked-reduction Cor 168, with r in R)
  thm170   at least k - 1 vertices of degree n - 2 (marked-reduction Thm 170)
  lit      a class of eulerian-cone Thm 2.3 that is decided here exactly: planar, Delta(B) <= 4,
           Delta(B - r) <= 3, 2-degenerate, B - r a forest.  (Treewidth <= 3 and K5-minor-free are not
           tested, so 'lit' undercounts.)
  lov      ret.c -L found a Lovasz decomposition and orientation that work
Prints counts of every combination that occurs, and the union of the proved conditions.
"""
import sys
from collections import Counter

import networkx as nx


def star_holds(B, r):
    n = B.number_of_nodes()
    k = n // 2
    N = list(B[r])
    for t in range(3, k):
        h = sum(1 for x in N if B.degree(x) >= 2 * t)
        if h // 2 > k + 1 - t:
            return False
    return True


def star2_holds(B, r):
    n = B.number_of_nodes()
    k = n // 2
    N = list(B[r])

    def h(t):
        return sum(1 for x in N if B.degree(x) >= 2 * t)

    for t in range(3, k):
        if h(t) // 2 <= k + 1 - t or h(t + 1) // 2 <= k + 1 - 2 * t:
            continue
        return False
    return True


def two_degenerate(B):
    return max(nx.core_number(B).values()) <= 2


def lit(B, r):
    if nx.check_planarity(B)[0]:
        return True
    if max(d for _, d in B.degree()) <= 4:
        return True
    G = B.copy()
    G.remove_node(r)
    if max(d for _, d in G.degree()) <= 3:
        return True
    if two_degenerate(B):
        return True
    if nx.is_forest(G):
        return True
    return False


def main():
    n = int(sys.argv[1])
    lov = {}
    for line in open(sys.argv[2]):
        g6, rest = line.split(None, 1)
        f = rest.split()
        lov[(g6, int(f[0]))] = f[1]
    k = n // 2
    cnt = Counter()
    tot = 0
    union = 0
    rows = []
    for (g6, r), st in lov.items():
        B = nx.from_graph6_bytes(g6.encode())
        assert B.degree(r) == n - 2
        u = sum(1 for _, d in B.degree() if d == n - 2)
        key = (
            star_holds(B, r),
            star2_holds(B, r),
            u >= k,
            u >= k - 1,
            lit(B, r),
            st,
        )
        cnt[key] += 1
        tot += 1
        union += key[1] or key[3] or key[4]
        rows.append((g6, r, key))
    print("n=%d degree-(n-2) roots: %d" % (n, tot))
    print("star star2 cor168 thm170 lit lov : count")
    for key in sorted(cnt):
        print(*key, ":", cnt[key])
    for name, i in (("star", 0), ("star2", 1), ("cor168", 2), ("thm170", 3), ("lit", 4)):
        print("%-6s %d" % (name, sum(c for kk, c in cnt.items() if kk[i])))
    for v in ("YES", "NO", "UNK"):
        print("lov %s %d" % (v, sum(c for kk, c in cnt.items() if kk[5] == v)))
    print("star2 or thm170 or lit: %d" % union)
    print("star2 or cor168 or lit: %d" % sum(c for kk, c in cnt.items() if kk[1] or kk[2] or kk[4]))
    print("star2 or lit: %d" % sum(c for kk, c in cnt.items() if kk[1] or kk[4]))
    print("none of star2, thm170, lit: %d (lov YES %d, NO %d, UNK %d)" % tuple(
        [sum(c for kk, c in cnt.items() if not (kk[1] or kk[3] or kk[4]))] +
        [sum(c for kk, c in cnt.items() if not (kk[1] or kk[3] or kk[4]) and kk[5] == v)
         for v in ("YES", "NO", "UNK")]))
    if len(sys.argv) > 3:
        with open(sys.argv[3], "w") as o:
            for g6, r, key in rows:
                o.write("%s %d %s\n" % (g6, r, " ".join(str(int(x)) if isinstance(x, bool) else x for x in key)))


if __name__ == "__main__":
    main()

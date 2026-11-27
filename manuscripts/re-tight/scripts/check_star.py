"""check_star.py FILE: test Theorem 3.1 against ret.c -T output.

ret.c -T enumerates every Lovasz decomposition D of G = B - r, orients every path so that its
trivial end is the end of smaller degree (ties by label), and reports minmu, the least size over
all D of a maximum matching between the paths and the trivial ends (path P ~ trivial b iff
b is not on P).  Theorem 3.1 asserts minmu >= k - 3 whenever (**) holds (and a fortiori (*)).
This script recomputes (*) and (**) from the graph and checks the implication at every root;
it also tabulates minmu >= k - 3 against the two conditions.
"""
import sys
from collections import Counter

import networkx as nx


def h(B, r, t):
    return sum(1 for x in B[r] if B.degree(x) >= 2 * t)


def star(B, r):
    k = B.number_of_nodes() // 2
    return all(h(B, r, t) // 2 <= k + 1 - t for t in range(3, k))


def star2(B, r):
    k = B.number_of_nodes() // 2
    for t in range(3, k):
        if h(B, r, t) // 2 <= k + 1 - t:
            continue
        if h(B, r, t + 1) // 2 <= k + 1 - 2 * t:
            continue
        return False
    return True


def main():
    cnt = Counter()
    bad = 0
    for line in open(sys.argv[1]):
        g6, rest = line.split(None, 1)
        f = rest.split()
        r = int(f[0])
        if f[1] != "DONE":
            cnt["UNK"] += 1
            continue
        mu = int(f[3].split("=")[1])
        need = int(f[4].split("=")[1])
        B = nx.from_graph6_bytes(g6.encode())
        s1, s2 = star(B, r), star2(B, r)
        ok = mu >= need
        cnt[(s1, s2, ok)] += 1
        if (s1 or s2) and not ok:
            bad += 1
            print("VIOLATION", g6, r, "minmu", mu, "need", need)
    print("(star, star2, every D works) : count")
    for kk in sorted(cnt, key=str):
        print(kk, cnt[kk])
    print("violations of Theorem 3.1:", bad)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()

"""zcheck.py RETZ_FILE...: independent re-decision of ret.c -z answers at small orders.

-z at a root r of degree n - 2 answers whether p(B) <= k - 1.  For every graph in the files we
decide p(B) <= k - 1 by our own exhaustive search (paths through the lowest remaining edge, both
orientations merged by requiring the lowest edge to be traversed from its lower end; pruning only
by the counting bounds below) and compare with every YES/NO line.
"""
import sys
from collections import Counter

sys.path.insert(0, __import__("os").path.dirname(__file__))
from g6 import parse_g6, edges  # noqa: E402


def decomposes(n, adj, p):
    """Does the graph decompose into at most p paths?"""
    R = {frozenset(e) for e in edges(n, adj)}
    rad = [set(a) for a in adj]

    def lb():
        odd = sum(1 for v in range(n) if len(rad[v]) % 2)
        mx = max((len(rad[v]) + 1) // 2 for v in range(n))
        return max(odd // 2, mx, 1 if R else 0)

    def rec(p):
        if not R:
            return True
        if p == 0 or lb() > p or len(R) > p * (n - 1):
            return False
        e = min(R, key=lambda f: tuple(sorted(f)))
        a, b = sorted(e)
        # all simple paths through edge ab: left part from a, right part from b
        out = []

        def ext(seq, vis, used, side_left):
            pass

        res = [False]

        def right(path, vis):
            c = path[-1]
            # try path as is
            for w in list(rad[c]):
                if w in vis:
                    continue
                f = frozenset((c, w))
                if f not in R:
                    continue
                R.discard(f); rad[c].discard(w); rad[w].discard(c)
                path.append(w); vis.add(w)
                if right(path, vis):
                    return True
                path.pop(); vis.discard(w)
                R.add(f); rad[c].add(w); rad[w].add(c)
            return rec(p - 1)

        def left(path, vis):
            c = path[0]
            for w in list(rad[c]):
                if w in vis:
                    continue
                f = frozenset((c, w))
                if f not in R:
                    continue
                R.discard(f); rad[c].discard(w); rad[w].discard(c)
                path.insert(0, w); vis.add(w)
                if left(path, vis):
                    return True
                path.pop(0); vis.discard(w)
                R.add(f); rad[c].add(w); rad[w].add(c)
            return right(path, vis)

        R.discard(e); rad[a].discard(b); rad[b].discard(a)
        ok = left([a, b], {a, b})
        R.add(e); rad[a].add(b); rad[b].add(a)
        return ok

    return rec(p)


def main():
    c = Counter()
    cache = {}
    for fn in sys.argv[1:]:
        for line in open(fn):
            f = line.split()
            g, st = f[0], f[2]
            if st not in ("YES", "NO"):
                continue
            n, adj = parse_g6(g)
            k = n // 2
            if g not in cache:
                cache[g] = decomposes(n, adj, k - 1)
            want = cache[g]
            c[(n, st, "agree" if want == (st == "YES") else "DISAGREE")] += 1
            if want != (st == "YES"):
                print("DISAGREE", g, f[1], st)
    for kk in sorted(c):
        print(kk, c[kk])


if __name__ == "__main__":
    main()

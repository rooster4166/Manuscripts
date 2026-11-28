"""h_bases8.py (audit A37): my own exhaustive check, no oracle, of the order-6/8 base claims:
  * Section 4: number of instances with a matching base (Phi a perfect matching of J[N(z)], r the
    root of its pair); the claim that EVERY perfect matching of J[N(z)] (1,512 at order 8) gives a
    matching base (some orientation of the other pairs and some Lovasz decomposition of M);
  * Section 5 (DL data): for every w in N(z) - r and every perfect matching M0 of J[N(z) - {r,w}],
    whether B - M0 has a Lovasz decomposition with every disjunction, and whether some pair is a
    pair of universal twins of its component of B - M0; claim: 2,280 twin-free choices all have a
    base, 153 twin choices none.  Also: instances with some floor matching base (session: 834 M).
usage: python3 h_bases8.py
"""
import sys
from collections import Counter

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from a37lib import adjacency, delete_vertex, g6_decode

DATA = "/home/user/Manuscripts/manuscripts/test2/data/t2_order6_8.txt"


def lovasz_gen(n, Eset, b):
    """Yield every decomposition of Eset into paths with exactly b[v] ends at v (b in {0,1})."""
    A = adjacency(n, Eset)
    need = [v for v in range(n) if b[v] == 1]

    def rec(rem, ended, acc):
        todo = [v for v in need if v not in ended]
        if not todo:
            if not rem:
                yield list(acc)
            return
        v = todo[0]
        stack = [([v], frozenset([v]), frozenset())]
        # DFS over simple paths from v
        def dfs(path, vis, used):
            u = path[-1]
            if len(path) >= 2 and b[u] == 1 and u not in ended:
                yield from rec(rem - used, ended | {v, u}, acc + [list(path)])
            for w in sorted(A[u]):
                e = frozenset((u, w))
                if e in rem and e not in used and w not in vis:
                    path.append(w)
                    yield from dfs(path, vis | {w}, used | {e})
                    path.pop()
        yield from dfs([v], frozenset([v]), frozenset())
    yield from rec(frozenset(Eset), frozenset(), [])


def perfect_matchings(vs, A):
    if not vs:
        yield []
        return
    a = vs[0]
    for b in vs[1:]:
        if b in A[a]:
            for pm in perfect_matchings([v for v in vs[1:] if v != b], A):
                yield [(a, b)] + pm


def ends_path(D):
    Q = {}
    for P in D:
        Q[P[0]] = P
        Q[P[-1]] = P
    return Q


def disj_ok(Q, pairs):
    return all((a not in Q[b]) or (b not in Q[a]) for a, b in pairs)


def univ_twins(n, Eset, a, b):
    A = adjacency(n, Eset)
    seen, st = {a}, [a]
    while st:
        u = st.pop()
        for w in A[u]:
            if w not in seen:
                seen.add(w)
                st.append(w)
    if b not in seen:
        return False
    return all(x in A[a] and x in A[b] for x in seen - {a, b})


def main():
    st = Counter()
    for line in open(DATA):
        g6, z, r = line.split()[:3]
        z, r = int(z), int(r)
        n, E = g6_decode(g6)
        A = adjacency(n, E)
        B = delete_vertex(E, z)
        T = sorted(A[z])
        # ---- matching base (forest lift with Phi a perfect matching of J[N(z)])
        pms = list(perfect_matchings(T, A))
        okpm = 0
        for pm in pms:
            Phi = {frozenset(p) for p in pm}
            M = {e for e in E if not (z in e and (set(e) - {z}).pop() != r)} - Phi
            a0 = [p[0] if p[1] == r else p[1] for p in pm if r in p][0]
            others = [p for p in pm if r not in p]
            b = [1] * n
            found = False
            for D in lovasz_gen(n, M, b):
                Q = ends_path(D)
                if r not in Q[a0] and disj_ok(Q, others):
                    found = True
                    break
            okpm += found
        st[(n, "perfect matchings of J[N(z)]")] += len(pms)
        st[(n, "  ... giving a matching base")] += okpm
        st[(n, "instances with a matching base")] += okpm > 0
        # ---- floor data (w, M0)
        anyfloor = False
        for w in T:
            if w == r:
                continue
            for pm in perfect_matchings([v for v in T if v not in (r, w)], A):
                G = B - {frozenset(p) for p in pm}
                AG = adjacency(n, G)
                b = [len(AG[v]) % 2 if v != z else 0 for v in range(n)]
                assert b[w] == 0 and sum(b) == n - 2
                twin = any(univ_twins(n, G, a, c) for a, c in pm)
                found = False
                for D in lovasz_gen(n, G, b):
                    if disj_ok(ends_path(D), pm):
                        found = True
                        break
                st[(n, "floor data", "twin" if twin else "twin-free", "base" if found else "NO base")] += 1
                anyfloor |= found
        st[(n, "instances with a floor matching base")] += anyfloor
        st[(n, "instances")] += 1
    for k in sorted(st, key=str):
        print(k, st[k])


if __name__ == "__main__":
    main()

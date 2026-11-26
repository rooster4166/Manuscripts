"""Test the faithful-descent property (FD) on small even-order graphs.

Even vertices E (|E| = e), odd vertices O (|O| = o).  For S subset of E let
"S is realisable" mean: some decomposition has exactly 2 ends at each vertex of
S, 0 at E - S, and exactly 1 at each odd vertex.  Such a decomposition has
(o + 2|S|)/2 paths.  Cai: S = E is realisable (faithful decomposition).

(FD): for every realisable S with |S| > e/2 and every r in S, there is u in S-r
with S - u realisable.  Descending from E gives, for every even r, a
realisable S containing r with |S| = e/2, i.e. n/2 paths exposing r: the
even-order rooted test, which is equivalent to Gallai.

We also record the weaker statement actually needed (FD-reach): every even r
lies in some realisable S of size e/2 reachable from E by such descents.
"""
import itertools
import sys
from functools import lru_cache

import networkx as nx

from pathnum import enumerate_paths, solve


def make_oracle(G):
    paths = enumerate_paths(G)
    E = [v for v in G if G.degree(v) % 2 == 0 and G.degree(v) > 0]
    O = [v for v in G if G.degree(v) % 2 == 1]
    cache = {}

    def realisable(S):
        S = frozenset(S)
        if S in cache:
            return cache[S]
        exact = {v: 1 for v in O}
        for v in E:
            exact[v] = 2 if v in S else 0
        r = solve(G, exact_ends=exact, paths=paths, time_limit=60, workers=1)
        ok = r.status in ("OPTIMAL", "FEASIBLE")
        cache[S] = ok
        return ok

    return E, O, realisable


def check(G):
    E, O, real = make_oracle(G)
    e = len(E)
    if e == 0:
        return None
    assert real(E), "Cai faithful decomposition missing?!"
    fd_fail = []
    # all realisable sets reachable from E by FD steps (any u), by level
    reach = {frozenset(E)}
    frontier = {frozenset(E)}
    for size in range(e, e // 2, -1):
        nxt = set()
        for S in frontier:
            for r in S:
                ok = False
                for u in S:
                    if u == r:
                        continue
                    T = S - {u}
                    if real(T):
                        ok = True
                        nxt.add(T)
                if not ok:
                    fd_fail.append((sorted(S), r))
        frontier = nxt
        reach |= nxt
    bottom = [S for S in reach if len(S) == e // 2]
    covered = set().union(*bottom) if bottom else set()
    unreached = [r for r in E if r not in covered]
    return fd_fail, unreached


if __name__ == "__main__":
    tot = fdbad = reachbad = 0
    for line in open(sys.argv[1]):
        G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(line.strip().encode()))
        res = check(G)
        if res is None:
            continue
        tot += 1
        fd_fail, unreached = res
        if fd_fail:
            fdbad += 1
            if fdbad <= 10:
                print("FD-FAIL", line.strip(), fd_fail[:4])
        if unreached:
            reachbad += 1
            print("REACH-FAIL", line.strip(), unreached)
    print(f"graphs with even vertices: {tot}; FD failures: {fdbad}; FD-reach failures: {reachbad}")

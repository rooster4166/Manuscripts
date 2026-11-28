"""Run the constructive proof of NA on every instance of a list of graphs.

usage: nauty-geng -c N | python3 run_na.py [--exact] [--brute] [--sets]

For every graph with all degrees odd, every ordered pair (y, x) with x ~ y:
  * classify: NA hypothesis (witness w in N(y) - N[x]); weak hypothesis (the component of y in
    G - x contains a vertex not adjacent to x); neither;
  * if the weak hypothesis holds: run na_construct with both steering methods (the farthest-vertex
    toggling of Lemmas 4.1/4.3, and the T-join/Euler trail) and verify each output independently;
  * --exact: decide the instance exactly (exact.avoid_exact), and check that it is good exactly when
    the weak hypothesis holds; --exact-neither: the same, only for the pairs outside the weak
    hypothesis (the others are certified by the construction);
  * --brute: also cross-check avoid_exact against brute-force enumeration (small graphs only);
  * --progress: print the running counts after every graph;
  * --sets: also run the packed-set form for every packed Y with y adjacent to one vertex of Y
    (|Y| <= 3) satisfying the weak hypothesis.
"""
import sys
from itertools import combinations

import nalib
import exact

args = set(sys.argv[1:])
stats = dict(graphs=0, allodd=0, pairs=0, na=0, weak=0, weak_not_na=0, neither=0,
             construct_ok=0, exact_good=0, exact_bad=0, mismatch=0, brute_checked=0,
             set_instances=0, set_ok=0, trail_bf=0)

for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    G = nalib.g6_decode(line)
    stats["graphs"] += 1
    if any(len(G[v]) % 2 == 0 for v in G):
        continue
    stats["allodd"] += 1
    exact.decomposable.cache_clear()
    brute = None
    if "--brute" in args:
        try:
            brute = exact.brute_all(G)
        except RuntimeError:
            brute = None
            print("brute force cap exceeded, skipped:", line, flush=True)
    for y in G:
        for x in sorted(G[y]):
            stats["pairs"] += 1
            na = any(w != x and w not in G[x] for w in G[y])
            H = {v: set(G[v]) - {x} for v in G if v != x}
            comp = next(c for c in nalib.components(H) if y in c)
            weak = any(v not in G[x] for v in comp)
            if na:
                stats["na"] += 1
                assert weak
            elif weak:
                stats["weak_not_na"] += 1
            else:
                stats["neither"] += 1
            if weak:
                stats["weak"] += 1
                for method in ("paper", "tjoin"):
                    D, W = nalib.na_construct(G, y, {x}, method)
                    ok, msg = nalib.check_na_output(G, D, y, {x})
                    if not ok:
                        print("CONSTRUCT FAIL", method, line, y, x, msg, flush=True)
                        sys.exit(1)
                stats["construct_ok"] += 1
                if "--trailbf" in args:
                    C = {v: set(H[v]) for v in comp}
                    assert nalib.trail_exists_bruteforce(C, y)
                    stats["trail_bf"] += 1
            if "--exact" in args or ("--exact-neither" in args and not weak):
                Q = exact.avoid_exact(G, y, {x})
                good = Q is not None
                stats["exact_good" if good else "exact_bad"] += 1
                if good != weak:
                    stats["mismatch"] += 1
                    print("MISMATCH", line, y, x, "good" if good else "bad", "weak" if weak else "notweak",
                          flush=True)
                if brute is not None:
                    bgood = any(
                        x not in next(P for P in dec if P[0] == y or P[-1] == y) for dec in brute)
                    assert bgood == good, ("brute disagrees", line, y, x)
                    stats["brute_checked"] += 1
            if "--sets" in args and weak:
                others = [v for v in G if v != y and v != x and v not in G[y]]
                for r in (1, 2):
                    for extra in combinations(others, r):
                        Y = {x, *extra}
                        if not nalib.packed(G, Y):
                            continue
                        NY = set()
                        for a in Y:
                            NY |= G[a]
                        Hs = {v: set(G[v]) - Y for v in G if v not in Y}
                        cs = next(c for c in nalib.components(Hs) if y in c)
                        if not any(v not in NY for v in cs):
                            continue
                        stats["set_instances"] += 1
                        D, W = nalib.na_construct(G, y, Y)
                        ok, msg = nalib.check_na_output(G, D, y, Y)
                        if not ok:
                            print("SET FAIL", line, y, Y, msg, flush=True)
                            sys.exit(1)
                        stats["set_ok"] += 1

    if "--progress" in args:
        print("graph", stats["allodd"], line, " ".join("%s=%d" % kv for kv in stats.items()), flush=True)

print(" ".join("%s=%d" % kv for kv in stats.items()), flush=True)

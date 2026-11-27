"""A16: exhaustive checks of the small examples of route-descent.tex, with an independent
enumerator of all path partitions (a16_core.partitions_with_profile, by transition systems).

  ex24     Example 24 (distance two): no Lovasz decomposition separates c, a; the displayed
           decomposition is a Lovasz decomposition with Q_c = c u1 avoiding a; with a leaf at z
           a separating decomposition exists.
  k4e      An all-odd analogue of Example 24 (K4 - e with two leaves), found by mode odd2.
  path     Remark 25, second bullet: on the path c z a the only Lovasz decomposition is the path.
  star     Remark 25, third bullet: leaves hung at the three leaves of K_{1,3}: some path always
           joins two of the hung leaves.
  odd2     Search for the smallest graphs with ALL degrees odd and a pair at distance exactly 2
           that no Lovasz decomposition separates (the manuscript's Example 24 has an even
           vertex; this shows distance three is needed even when all degrees are odd).
  oracle   Cross-check the oracle's S query (tools/route_ext.c) against the enumerator.

Usage: python3 a16_enum.py MODE [args]
"""
import itertools
import random
import sys

import a16_core as C


def graph(edge_list):
    adj = {}
    for u, v in edge_list:
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)
    return adj


def separates(D, c, a):
    return not any(c in P and a in P for P in D)


def ex24():
    E = [("z", "u1"), ("z", "u2"), ("u1", "c"), ("u1", "a"), ("u2", "c"), ("u2", "a"),
         ("c", "lc"), ("a", "la")]
    K = graph(E)
    assert C.even_set(K) == ["z"] and C.dist(K, "c", "a") == 2
    Ds = list(C.lovasz_decompositions(K))
    nsep = sum(separates(D, "c", "a") for D in Ds)
    print(f"Example 24: {len(Ds)} Lovasz decompositions, {nsep} separate c and a")
    assert Ds and nsep == 0
    shown = [["c", "u1"], ["lc", "c", "u2", "z", "u1", "a"], ["u2", "a", "la"]]
    C.check_partition(K, shown, C.lovasz_profile(K))
    (Qc,) = [P for P in shown if "c" in (P[0], P[-1])]
    assert "a" not in Qc
    print("  displayed decomposition: valid Lovasz decomposition, Q_c =", Qc)
    # L1 in the one-even-vertex sense: number of decompositions with a not in Q_c
    nl1 = sum(all("a" not in P for P in D if "c" in (P[0], P[-1])) for D in Ds)
    print(f"  decompositions with a not in Q_c: {nl1}")
    K2 = graph(E + [("z", "lz")])
    assert C.even_set(K2) == []
    Ds2 = list(C.lovasz_decompositions(K2))
    sep2 = [D for D in Ds2 if separates(D, "c", "a")]
    print(f"  with a leaf at z: {len(Ds2)} Lovasz decompositions, {len(sep2)} separate c and a;"
          f" e.g. {sep2[0] if sep2 else None}")
    assert sep2


def k4e():
    """All degrees odd, dist(c, a) = 2, no separating Lovasz decomposition: K4 - ca plus a leaf at
    each of c and a (6 vertices, 7 edges). Example 24 with the even vertex z contracted into the
    edge u1 u2; the manuscript's argument applies verbatim."""
    E = [("u1", "u2"), ("u1", "c"), ("u1", "a"), ("u2", "c"), ("u2", "a"), ("c", "lc"), ("a", "la")]
    K = graph(E)
    assert C.even_set(K) == [] and C.dist(K, "c", "a") == 2
    Ds = list(C.lovasz_decompositions(K))
    nsep = sum(separates(D, "c", "a") for D in Ds)
    nl1 = sum(all("a" not in P for P in D if "c" in (P[0], P[-1])) for D in Ds)
    ns1 = sum(all("a" not in P for P in D if "c" in (P[0], P[-1])) and
              all("c" not in P for P in D if "a" in (P[0], P[-1])) for D in Ds)
    print(f"K4 - e with leaves at c, a (all odd, dist 2): {len(Ds)} Lovasz decompositions, "
          f"{nsep} separate c and a; {nl1} have a not in Q_c; {ns1} have both a not in Q_c and "
          f"c not in Q_a")
    assert Ds and nsep == 0


def path_cza():
    K = graph([("c", "z"), ("z", "a")])
    Ds = list(C.lovasz_decompositions(K))
    print("path c z a: Lovasz decompositions", Ds)
    assert len(Ds) == 1 and Ds[0] in ([["c", "z", "a"]], [["a", "z", "c"]])


def star():
    E = [("w", "c1"), ("w", "c2"), ("w", "c3"), ("c1", "l1"), ("c2", "l2"), ("c3", "l3")]
    K = graph(E)
    Ds = list(C.lovasz_decompositions(K))
    bad = [D for D in Ds if C.meets_once(D, ["l1", "l2", "l3"])]
    print(f"star K13 with hung leaves: {len(Ds)} Lovasz decompositions, {len(bad)} meet "
          f"{{l1,l2,l3}} at most once per path; packed: {C.packed(K, ['l1', 'l2', 'l3'])}")
    assert not bad


def all_graphs(n):
    V = list(range(n))
    pairs = list(itertools.combinations(V, 2))
    for mask in range(1 << len(pairs)):
        adj = {v: set() for v in V}
        for i, (u, v) in enumerate(pairs):
            if mask >> i & 1:
                adj[u].add(v)
                adj[v].add(u)
        yield adj


def canon(adj):
    n = len(adj)
    best = None
    for perm in itertools.permutations(range(n)):
        key = tuple(sorted(tuple(sorted((perm[u], perm[v]))) for u in adj for v in adj[u] if u < v))
        if best is None or key < best:
            best = key
    return best


def odd2(nmax=6):
    """All graphs on n <= nmax vertices with every degree odd (no isolated vertices)."""
    found = []
    for n in range(2, nmax + 1, 2):
        seen = set()
        cnt_pairs = 0
        for adj in all_graphs(n):
            if any(len(adj[v]) % 2 == 0 for v in adj):
                continue
            key = canon(adj) if n <= 6 else None
            if key in seen:
                continue
            seen.add(key)
            Ds = None
            for c in adj:
                for a in adj:
                    if c < a and C.dist(adj, c, a) == 2:
                        cnt_pairs += 1
                        if Ds is None:
                            Ds = list(C.lovasz_decompositions(adj))
                        if not any(separates(D, c, a) for D in Ds):
                            found.append((n, sorted((u, v) for u in adj for v in adj[u] if u < v), c, a))
        print(f"n = {n}: {len(seen)} all-odd graphs (up to iso), {cnt_pairs} distance-2 pairs, "
              f"non-separable so far: {len(found)}")
    for f in found[:10]:
        print("  non-separable:", f)
    return found


def odd2_random(trials, seed, nmin=8, nmax=10):
    """Random all-odd graphs of order nmin..nmax: find distance-2 pairs that cannot be separated
    (oracle S query, exhaustive); report the smallest by edge count."""
    rng = random.Random(seed)
    best = None
    tot = bad = 0
    for _ in range(trials):
        n = rng.choice(range(nmin, nmax + 1, 2))
        adj = C.make_odd(C.random_graph(n, rng.uniform(0.2, 0.5), rng), rng, allow_isolated=False)
        if any(not adj[v] for v in adj):
            continue
        prs = [(c, a) for c in adj for a in adj if c < a and C.dist(adj, c, a) == 2]
        if not prs:
            continue
        c, a = rng.choice(prs)
        tot += 1
        if not C.oracle_sep(adj, C.lovasz_profile(adj), [(c, a)]):
            bad += 1
            m = len(C.edges(adj))
            if best is None or m < best[0]:
                best = (m, len(adj), sorted((u, v) for u in adj for v in adj[u] if u < v), c, a)
    print(f"random all-odd, n = {nmin}-{nmax}: {bad} of {tot} distance-2 pairs not separable")
    print("smallest found:", best)
    return best


def oracle_check(trials, seed):
    rng = random.Random(seed)
    agree = 0
    for _ in range(trials):
        n = rng.randint(4, 8)
        adj = C.random_one_even(n, rng.uniform(0.25, 0.6), rng)
        if not C.edges(adj) or len(C.edges(adj)) > 11:
            continue
        V = list(adj)
        c, a = rng.sample(V, 2)
        b = C.lovasz_profile(adj)
        ex = any(separates(D, c, a) for D in C.partitions_with_profile(adj, b))
        orc = C.oracle_sep(adj, b, [(c, a)])
        assert ex == orc, (adj, c, a, ex, orc)
        agree += 1
    print(f"oracle S query agrees with the enumerator on {agree} random instances")


def main():
    mode = sys.argv[1]
    if mode == "ex24":
        ex24()
    elif mode == "path":
        path_cza()
    elif mode == "star":
        star()
    elif mode == "odd2":
        odd2(int(sys.argv[2]) if len(sys.argv) > 2 else 6)
    elif mode == "odd2r":
        odd2_random(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
    elif mode == "oracle":
        oracle_check(int(sys.argv[2]), int(sys.argv[3]))
    elif mode == "k4e":
        k4e()
    elif mode == "all":
        ex24()
        k4e()
        path_cza()
        star()
        oracle_check(300, 1)
    else:
        raise SystemExit("unknown mode")


if __name__ == "__main__":
    main()

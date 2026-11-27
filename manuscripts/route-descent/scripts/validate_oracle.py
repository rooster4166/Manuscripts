"""Validate tools/route_ext.c.

1. P-queries agree with tools/realis.c on random simple profiles (n <= 12).
2. P- and X-queries agree with an independent brute force that enumerates every partition of
   E(G) into paths (small graphs), and every witness passes rd_lib.check_partition.

Usage: python3 validate_oracle.py [count]
"""
import os
import random
import subprocess
import sys
import tempfile

import networkx as nx

import rd_lib as L


def all_partitions(G):
    """Every partition of E(G) into simple paths (each exactly once)."""
    E = sorted(tuple(sorted(e)) for e in G.edges())

    def paths_through(rem, e):
        u, v = e
        adj = {}
        for x, y in rem:
            adj.setdefault(x, []).append(y)
            adj.setdefault(y, []).append(x)
        res = []

        def grow_right(path, used):
            yield path, used
            t = path[-1]
            for w in adj.get(t, []):
                f = tuple(sorted((t, w)))
                if w not in path and f in rem and f not in used:
                    yield from grow_right(path + [w], used | {f})

        def grow_left(path, used):
            yield path, used
            t = path[0]
            for w in adj.get(t, []):
                f = tuple(sorted((t, w)))
                if w not in path and f in rem and f not in used:
                    yield from grow_left([w] + path, used | {f})

        for p1, u1 in grow_right([u, v], {e}):
            for p2, u2 in grow_left(p1, u1):
                res.append((p2, u2))
        return res

    def rec(rem):
        if not rem:
            yield []
            return
        e = min(rem)
        for p, used in paths_through(rem, e):
            for rest in rec(rem - used):
                yield [p] + rest

    yield from rec(frozenset(E))


def ends_of(G, part):
    b = [0] * G.number_of_nodes()
    for P in part:
        b[P[0]] += 1
        b[P[-1]] += 1
    return b


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(7)
    d = tempfile.mkdtemp()
    rb = os.path.join(d, "realis")
    subprocess.run(["gcc", "-O2", "-o", rb, os.path.join(L.TOOLS, "realis.c")], check=True)
    pr = subprocess.Popen([rb], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    agree = 0
    for _ in range(count):
        n = rng.choice([6, 8, 10, 12])
        G = nx.gnp_random_graph(n, rng.uniform(0.25, 0.7), seed=rng.randrange(10**9))
        if not nx.is_connected(G) or G.number_of_edges() > 64:
            continue
        Ev = L.even_vertices(G)
        S = [v for v in Ev if rng.random() < 0.5]
        b = L.simple_profile(G, S)
        line = "P " + L._graph_str(G) + " " + " ".join(map(str, b))
        pr.stdin.write(line + "\n")
        pr.stdin.flush()
        r1 = pr.stdout.readline().strip() == "1"
        r2 = L.realisable(G, b)
        assert r1 == r2, (sorted(G.edges()), b)
        if r2:
            L.witness(G, b)
        agree += 1
    print(f"P-queries: {agree} agree with realis.c")

    # brute force on small graphs: every profile of every partition; X-queries
    nP = nX = 0
    for _ in range(count):
        n = rng.choice([4, 5, 6, 7])
        G = nx.gnp_random_graph(n, rng.uniform(0.3, 0.8), seed=rng.randrange(10**9))
        if G.number_of_edges() == 0 or G.number_of_edges() > 10:
            continue
        parts = list(all_partitions(G))
        profs = {}
        for part in parts:
            profs.setdefault(tuple(ends_of(G, part)), []).append(part)
        # P: random profiles (including non-realisable)
        for _ in range(6):
            b = [rng.randrange(0, min(3, G.degree(v)) + 1) for v in range(n)]
            truth = tuple(b) in profs
            assert L.realisable(G, b) == truth
            nP += 1
        for b, ps in [kv for kv in profs.items() if max(kv[0]) <= 3][:8]:
            assert L.realisable(G, list(b))
            nP += 1
            for c in range(n):
                if b[c] == 0:
                    continue
                for _ in range(3):
                    forbid = [x for x in range(n) if x != c and rng.random() < 0.3]
                    truth = any(any(c in (P[0], P[-1]) and not set(P) & set(forbid) for P in part)
                                for part in ps)
                    assert L.ext(G, list(b), c, forbid) == truth, (sorted(G.edges()), b, c, forbid)
                    if truth:
                        L.witness(G, list(b), c, forbid)
                    nX += 1
    print(f"brute force: {nP} P-queries and {nX} X-queries agree")


if __name__ == "__main__":
    main()


def validate_C(count=200, seed=9):
    """C-queries against brute force: random constraint masks on small graphs."""
    rng = random.Random(seed)
    nC = 0
    for _ in range(count):
        n = rng.choice([4, 5, 6, 7])
        G = nx.gnp_random_graph(n, rng.uniform(0.3, 0.8), seed=rng.randrange(10**9))
        if G.number_of_edges() == 0 or G.number_of_edges() > 10:
            continue
        parts = list(all_partitions(G))
        for _ in range(6):
            b = [G.degree(v) % 2 if rng.random() < 0.7 else rng.randrange(0, 3) for v in range(n)]
            crv = [(1 << v) | (sum(1 << x for x in range(n) if rng.random() < 0.25)) for v in range(n)]

            def okpath(P):
                s, w = P[0], P[-1]
                pm = sum(1 << x for x in P)
                return (pm & crv[s]) == (1 << s) and (pm & crv[w]) == (1 << w) and (crv[s] & crv[w]) == 0
            truth = any(ends_of(G, part) == b and all(okpath(P) for P in part) for part in parts)
            r = L._query("C " + L._graph_str(G) + " " + " ".join(map(str, b)) + " " + " ".join(map(str, crv)))
            assert (r == "1") == truth, (sorted(G.edges()), b, crv)
            nC += 1
    print(f"brute force: {nC} C-queries agree")


if __name__ == "__main__" and len(sys.argv) > 2 and sys.argv[2] == "C":
    validate_C()


def validate_A(count=200, seed=10):
    rng = random.Random(seed)
    nA = 0
    for _ in range(count):
        n = rng.choice([4, 5, 6, 7])
        G = nx.gnp_random_graph(n, rng.uniform(0.3, 0.8), seed=rng.randrange(10**9))
        if G.number_of_edges() == 0 or G.number_of_edges() > 10:
            continue
        parts = list(all_partitions(G))
        for _ in range(6):
            b = [G.degree(v) % 2 if rng.random() < 0.7 else rng.randrange(0, 3) for v in range(n)]
            X = {v: {x for x in range(n) if x != v and rng.random() < 0.3} for v in range(n)}

            def okpath(P):
                return not (set(P) & X[P[0]]) and not (set(P) & X[P[-1]])
            truth = any(ends_of(G, part) == b and all(okpath(P) for P in part) for part in parts)
            assert L.avoid(G, b, X) == truth, (sorted(G.edges()), b, X)
            nA += 1
    print(f"brute force: {nA} A-queries agree")


if __name__ == "__main__" and len(sys.argv) > 2 and sys.argv[2] == "A":
    validate_A()

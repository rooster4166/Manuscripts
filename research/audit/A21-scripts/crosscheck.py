"""crosscheck.py -- audit A21: compare ts.c (or ts2.c: argv[2]) with the naive enumerator naive.py.

usage: python3 crosscheck.py LIMIT [ts|ts2]

For every connected graph of order 3..7 with at most one vertex of positive even degree whose naive
search space (product of per-vertex pairing counts) is at most LIMIT, compare, for every query:
  T x y (every edge, d(x) odd), S (u, z) in the graph, A c {a} and A c {a1, a2} for all c odd.
Also graphs with an isolated vertex removed are included implicitly (geng -c is connected).
"""
import sys, os, subprocess, itertools, math
import networkx as nx
from naive import lovasz_decomps
from exhaust import Solver

HERE = os.path.dirname(os.path.abspath(__file__))
LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
SOLVER = sys.argv[2] if len(sys.argv) > 2 else "ts"


def npair(d):
    # pairings leaving d mod 2 unpaired: (d-1)!! for even d, d!! for odd d
    r = 1
    k = d if d % 2 else d - 1
    while k > 1:
        r *= k
        k -= 2
    return r


def main():
    S = Solver(os.path.join(HERE, SOLVER))
    nq = ng = mism = 0
    for N in range(3, 8):
        for line in subprocess.run(["nauty-geng", "-cq", str(N)], capture_output=True, text=True).stdout.split():
            G = nx.from_graph6_bytes(line.encode())
            ev = [v for v in G if G.degree(v) % 2 == 0 and G.degree(v) > 0]
            if len(ev) > 1:
                continue
            if math.prod(npair(G.degree(v)) for v in G) > LIMIT:
                continue
            ng += 1
            E = list(G.edges())
            D = lovasz_decomps(N, E)
            sets = [[set(P) for P in d] for d in D]
            ends = []
            for d in D:
                e = {}
                for P in d:
                    e[P[0]] = (P[1], set(P))
                    e[P[-1]] = (P[-2], set(P))
                ends.append(e)
            odd = [v for v in G if G.degree(v) % 2]
            for x in odd:
                for y in G[x]:
                    want = int(any(e[x][0] == y for e in ends))
                    got = S.ask(G, f"T {x} {y}")
                    nq += 1
                    if want != got:
                        mism += 1; print("MISMATCH T", line, x, y, want, got)
            for a, b in itertools.combinations(sorted(G), 2):
                want = int(any(all(not (a in P and b in P) for P in d) for d in sets))
                got = S.ask(G, f"S 1 {a} {b}")
                nq += 1
                if want != got:
                    mism += 1; print("MISMATCH S", line, a, b, want, got)
            for c in odd:
                others = [v for v in G if v != c]
                for k in (1, 2):
                    for A in itertools.combinations(others, k):
                        want = int(any(not (set(A) & e[c][1]) for e in ends))
                        got = S.ask(G, f"A {c} {k} " + " ".join(map(str, A)))
                        nq += 1
                        if want != got:
                            mism += 1; print("MISMATCH A", line, c, A, want, got)
            # existence (Lovasz's theorem)
            got = S.ask(G, "L"); nq += 1
            if got != int(bool(D)):
                mism += 1; print("MISMATCH L", line)
    print(f"crosscheck: graphs={ng} queries={nq} mismatches={mism}")


if __name__ == "__main__":
    main()

"""Exact check of the prescribed-end floor bound in odd order.

For every connected graph G of odd order N (graph6 file), with Delta(EV(G)) <= 3, and every
vertex y of even degree, decide whether G has a partition into at most (N-1)/2 paths with an end
at y (pathnum.solve with budget and min_ends).  Prints every failure with its data:
the even subgraph, whether G is SET, and the number e of even vertices.

Usage: python3 exact_prescribed.py FILE.g6 [maxdeg=3]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..', 'tools'))
import networkx as nx
from pathnum import solve, enumerate_paths


def ev(G):
    return [v for v in G if G.degree(v) % 2 == 0 and G.degree(v) > 0]


def is_set(G):
    E = ev(G)
    H = G.subgraph(E)
    if len(E) != 3 or H.number_of_edges() != 3:
        return False
    return all(sum(1 for w in G[v] if w in E) >= 2 for v in G if v not in E)


def main():
    path = sys.argv[1]
    maxdeg = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    gs = nx.read_graph6(path)
    if not isinstance(gs, list):
        gs = [gs]
    tested = fails = 0
    for G in gs:
        N = G.number_of_nodes()
        E = ev(G)
        H = G.subgraph(E)
        if E and max(dict(H.degree()).values()) > maxdeg:
            continue
        P = enumerate_paths(G)
        for y in E:
            tested += 1
            r = solve(G, budget=(N - 1) // 2, min_ends={y: 1}, paths=P, workers=1)
            if r.status not in ("OPTIMAL", "FEASIBLE"):
                fails += 1
                print("FAIL", nx.to_graph6_bytes(G, header=False).strip().decode(),
                      "y", y, "e", len(E), "SET", is_set(G),
                      "EV-edges", sorted(H.edges()), "deg", dict(G.degree()), flush=True)
    print(f"tested (G,y) pairs: {tested}, failures: {fails}", flush=True)


if __name__ == "__main__":
    main()

"""Second proof of Theorem 21 (cut selection) via one auxiliary graph.

(1) Pairing lemma, cut form: for any finite graph Gamma, the odd vertices have a pairing pi with
    sigma_pi(S) <= |delta_Gamma(S)| for every vertex set S.  Proof by deleting an edge xy and re-pairing
    (triangle inequality of the cut indicator) -- implemented below exactly as in the proof.
(2) B on V x V: copy v carries F^v (F = G - J, J a T-join for T = Ev); for each J-edge vx the edge
    (v,x)-(x,v).  Odd(B) = {(v,v) : v in Ev}.  For v and Y not containing v, the set
    S = {(u,w): u != v, u in Y} u {(v,w): w in Y} has |delta_B(S)| = |delta_{G^v}(Y)|.
So the pairing of Odd(B) given by (1) is a good pairing of Ev.  The script checks the parity claim,
the cut identity, and goodness against the enumeration, for all connected graphs of order <= 8.
"""
import random
import sys

import networkx as nx

import emm_lib as L
from certificates import good
from construction import tree_tjoin


def pair_by_deletion(Gam):
    """Lemma (1): returns a dict pairing the odd-degree vertices of Gam, built by edge deletion."""
    edges = list(Gam.edges())
    pi = {}
    H = nx.Graph()
    H.add_nodes_from(Gam)
    # build up from the empty graph, adding edges one at a time (the reverse of deletion)
    for x, y in edges:
        H.add_edge(x, y)
        # odd set changes by {x, y}; update pi as in the proof (read backwards: H' = H - xy)
        ox, oy = x in pi, y in pi          # in pi  <=>  odd in H - xy
        if ox and oy:
            a, b = pi[x], pi[y]
            if a == y:
                del pi[x], pi[y]
            else:
                del pi[x], pi[y]
                pi[a], pi[b] = b, a
        elif ox:
            a = pi.pop(x)
            pi[y], pi[a] = a, y
        elif oy:
            b = pi.pop(y)
            pi[x], pi[b] = b, x
        else:
            pi[x], pi[y] = y, x
    assert set(pi) == {u for u in Gam if Gam.degree(u) % 2}
    return pi


def build_B(G, J):
    n = G.number_of_nodes()
    F = nx.Graph()
    F.add_nodes_from(G)
    F.add_edges_from(e for e in G.edges() if frozenset(e) not in J)
    B = nx.Graph()
    B.add_nodes_from((v, w) for v in G for w in G)
    for v in G:
        for a, c in F.edges():
            if v not in (a, c):
                B.add_edge((v, a), (v, c))
        for w in G:
            if w != v and not G.has_edge(v, w):
                B.add_edge((v, v), (v, w))
    for e in J:
        a, c = tuple(e)
        B.add_edge((a, c), (c, a))
    return B


def check(G, F_feas, rng):
    n = G.number_of_nodes()
    Ev = L.even_vertices(G)
    H = G.copy()
    for u, w in H.edges():
        H[u][w]["weight"] = rng.random()
    J = tree_tjoin(nx.minimum_spanning_tree(H), Ev)
    B = build_B(G, J)
    odd = {x for x in B if B.degree(x) % 2}
    assert odd == {(v, v) for v in Ev}, "Odd(B) is not the diagonal over Ev"
    pi = pair_by_deletion(B)
    P = {(a[0], pi[a][0]) for a in pi if a[0] < pi[a][0]}
    # spot-check the cut identity on random (v, Y)
    for _ in range(20):
        v = rng.randrange(n)
        Y = {u for u in G if u != v and rng.random() < .5}
        S = {(u, w) for u in G for w in G if (u != v and u in Y) or (u == v and w in Y)}
        cutB = sum(1 for a, c in B.edges() if (a in S) != (c in S))
        Gv = nx.Graph([(a, c) for a, c in G.edges() if v not in (a, c)])
        Gv.add_nodes_from(G)
        Gv.add_edges_from((v, w) for w in G if w != v and not G.has_edge(v, w))
        cutGv = sum(1 for a, c in Gv.edges() if (a in Y) != (c in Y))
        assert cutB == cutGv, "cut identity fails"
    return good(sorted(P), F_feas)


def main():
    rng = random.Random(3)
    for N in map(int, sys.argv[1:] or ["6", "8"]):
        graphs = L.all_connected(N)
        bad = sum(1 for G, F in zip(graphs, L.cut_feasible(graphs)) if not check(G, F, rng))
        print(f"order {N}: {len(graphs)} graphs, {bad} pairings not good", flush=True)


if __name__ == "__main__":
    main()

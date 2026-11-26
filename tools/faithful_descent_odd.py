"""Odd-order analogue of faithful descent: is there a chain
E = S_e > S_{e-1} > ... > S_{(e-1)/2} of realisable sets (each obtained by
removing one vertex)?  The bottom level has floor(n/2) paths, so a chain gives
the floor bound.  Odd semi-cliques must fail.  Also reports graphs whose floor
holds but whose chain fails (descent strictly stronger than the floor).
"""
import sys
import networkx as nx
from faithful_descent import make_oracle
from pathnum import path_number


def is_odd_semi_clique(G):
    n = G.number_of_nodes()
    if n % 2 == 0:
        return False
    return n * (n - 1) // 2 - G.number_of_edges() <= n // 2 - 1


def chain_exists(G):
    E, O, real = make_oracle(G)
    e = len(E)
    frontier = {frozenset(E)}
    for size in range(e, e // 2, -1):
        nxt = set()
        for S in frontier:
            for u in S:
                T = S - {u}
                if T not in nxt and real(T):
                    nxt.add(T)
        if not nxt:
            return False
        frontier = nxt
    return True


if __name__ == "__main__":
    tot = 0
    out = {"chain ok": 0, "chain fails, semi-clique": 0, "chain fails, floor fails, not semi-clique": 0,
           "chain fails, floor holds": 0}
    for line in open(sys.argv[1]):
        G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(line.strip().encode()))
        if not any(G.degree(v) % 2 == 0 for v in G):
            continue
        tot += 1
        if chain_exists(G):
            out["chain ok"] += 1
            continue
        if is_odd_semi_clique(G):
            out["chain fails, semi-clique"] += 1
            continue
        p = path_number(G)
        if p > G.number_of_nodes() // 2:
            out["chain fails, floor fails, not semi-clique"] += 1
            print("BP-COUNTEREXAMPLE?!", line.strip(), p)
        else:
            out["chain fails, floor holds"] += 1
            print("chain-fail-floor-holds", line.strip(), "p=", p)
    print(tot, out)

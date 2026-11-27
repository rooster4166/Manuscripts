"""Instances for PTM_3 at a vertex of degree six (the first open rung, T(6)-i).

Reads graphs J (graph6) from stdin.  For every vertex z of degree 6 that is the only even vertex
of J, with J 3-connected, prints g6(J - z) (vertices relabelled 0..n-2 in order).  The even
vertices of J - z are exactly N(z), so `ptm p 3` on these lines tests all 15 perfect matchings F
of N(z) (pairs adjacent in J - z are F-edges parallel to G'-edges, marked * in the output).

usage: gen_d6.py [random COUNT N SEED]
  without arguments: filter stdin;
  random: COUNT random 3-connected J of order N with degree sequence (6, 3, ..., 3, 5?) drawn from
  the configuration model (simple graphs kept), one even vertex of degree 6.
"""
import sys, random
import networkx as nx


def emit(J, z, seen=None):
    H = J.copy()
    H.remove_node(z)
    H = nx.convert_node_labels_to_integers(H, ordering='sorted')
    s = nx.to_graph6_bytes(H, header=False).decode().strip()
    print(s, flush=False)


def ok(J, z):
    if J.degree(z) != 6:
        return False
    if any(J.degree(v) % 2 == 0 for v in J if v != z):
        return False
    return nx.node_connectivity(J) >= 3


def main():
    if len(sys.argv) > 1 and sys.argv[1] == 'random':
        count, n, seed = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        rng = random.Random(seed)
        made = 0
        while made < count:
            # degrees: z = 6, others odd in {3, 5}; total even
            degs = [6] + [rng.choice((3, 3, 3, 5)) for _ in range(n - 1)]
            if sum(degs) % 2:
                continue
            G = nx.Graph(nx.configuration_model(degs, seed=rng.randrange(1 << 30)))
            G.remove_edges_from(nx.selfloop_edges(G))
            if [G.degree(v) for v in range(n)] != degs:
                continue
            if not ok(G, 0):
                continue
            made += 1
            emit(G, 0)
        return
    for line in sys.stdin:
        s = line.strip()
        if not s or s.startswith('>'):
            continue
        J = nx.from_graph6_bytes(s.encode())
        ev = [v for v in J if J.degree(v) % 2 == 0]
        if len(ev) != 1:
            continue
        z = ev[0]
        if ok(J, z):
            emit(J, z)


if __name__ == '__main__':
    main()

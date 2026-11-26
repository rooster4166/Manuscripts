"""Random consistency check of the five-even floor theorem on concrete hosts.

For each labelled rim (one universal vertex 0, rim of max degree <= 2) build random hosts W of
odd order N: T = {0..4} even with W[T] = the core, all other vertices odd.  With "leaf", vertex
N-1 is a leaf whose support is an odd exterior vertex.  Checks p(W) <= (N-1)/2 with the circuit
solver tools/pathnum2.py (and verifies the returned partition).

Usage: python3 random_hosts.py N trials [leaf|noleaf] [bowtie]
"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'tools'))
import networkx as nx
from pathnum import verify_partition
from pathnum2 import decompose
from certgen import rim_edges, rim_ok, is_bowtie


def host(code, N, leaf, rng, p):
    G = nx.Graph()
    G.add_nodes_from(range(N))
    G.add_edges_from([(0, t) for t in (1, 2, 3, 4)] + rim_edges(code))
    X = list(range(5, N - 1 if leaf else N))
    for a in X:
        for b in list(range(5)) + X:
            if b < a and rng.random() < p:
                G.add_edge(a, b)
    if leaf:
        s = rng.choice(X)
        G.add_edge(N - 1, s)
    # parity of T: toggle an edge to an exterior vertex (never the leaf)
    for t in range(5):
        if G.degree(t) % 2:
            w = rng.choice(X)
            if G.has_edge(t, w):
                G.remove_edge(t, w)
            else:
                G.add_edge(t, w)
    bad = [a for a in X if G.degree(a) % 2 == 0]
    rng.shuffle(bad)
    for a, b in zip(bad[::2], bad[1::2]):
        if G.has_edge(a, b):
            G.remove_edge(a, b)
        else:
            G.add_edge(a, b)
    if leaf and G.degree(G.nodes and N - 1) != 1:
        return None
    ev = [v for v in G if G.degree(v) % 2 == 0]
    if sorted(ev) != [0, 1, 2, 3, 4] or not nx.is_connected(G):
        return None
    if leaf and G.degree(next(iter(G[N - 1]))) % 2 == 0:
        return None
    return G


def main():
    N, trials = int(sys.argv[1]), int(sys.argv[2])
    leaf = len(sys.argv) > 3 and sys.argv[3] == 'leaf'
    only_bow = len(sys.argv) > 4 and sys.argv[4] == 'bowtie'
    rng = random.Random(N * 1000 + trials + leaf)
    codes = [c for c in range(64) if rim_ok(c) and (is_bowtie(c) or not only_bow)]
    done = fail = 0
    while done < trials:
        code = rng.choice(codes)
        G = host(code, N, leaf, rng, rng.uniform(0.2, 0.7))
        if G is None:
            continue
        st, P = decompose(G, (N - 1) // 2, time_limit=60, workers=2)
        done += 1
        if P is None or not verify_partition(G, P):
            fail += 1
            print('FAIL', st, code, nx.to_graph6_bytes(G, header=False).strip().decode(), flush=True)
    print(f'N={N} leaf={leaf} bowtie-only={only_bow}: {done} hosts, {fail} without a floor partition',
          flush=True)


if __name__ == '__main__':
    main()

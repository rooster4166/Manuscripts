"""All connected graphs of order n (odd) with exactly one even vertex, up to isomorphism.

Every connected graph on n vertices is H + v for a connected H on n-1 vertices (delete a
non-cut vertex v).  We extend every graph of data/conn{n-1}.g6 by a vertex with every
nonempty neighbourhood, keep those with exactly one even vertex, and remove isomorphic
copies (WL hash + exact test).  Output: graph6, one per line.
"""
import sys, itertools
import networkx as nx

n = int(sys.argv[1])
src = f'../../../data/conn{n-1}.g6'
buckets = {}
out = []
cand = 0
for line in open(src, 'rb'):
    H = nx.from_graph6_bytes(line.strip())
    H = nx.convert_node_labels_to_integers(H)
    k = n - 1
    degs = [H.degree(v) for v in range(k)]
    for mask in range(1, 1 << k):
        # parity of new vertex
        dv = bin(mask).count('1')
        ev = (dv % 2 == 0)
        for v in range(k):
            d = degs[v] + ((mask >> v) & 1)
            if d % 2 == 0:
                if ev: ev = 2; break
                ev = True
        if ev is not True:
            continue
        cand += 1
        G = H.copy(); G.add_node(k)
        G.add_edges_from((k, v) for v in range(k) if (mask >> v) & 1)
        key = nx.weisfeiler_lehman_graph_hash(G, iterations=4) + '|' + str(G.number_of_edges())
        lst = buckets.setdefault(key, [])
        if any(nx.is_isomorphic(G, K) for K in lst):
            continue
        lst.append(G); out.append(G)
for G in out:
    sys.stdout.write(nx.to_graph6_bytes(G, header=False).decode())
sys.stderr.write(f'n={n}: {cand} candidates, {len(out)} graphs with exactly one even vertex\n')

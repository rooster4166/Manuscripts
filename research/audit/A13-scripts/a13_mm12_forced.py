#!/usr/bin/env python3
"""Audit A13: in each order-12 EMM counterexample, a bridge belongs to every T-join (T = Ev) iff
one of its sides holds an odd number of even vertices. Find the pairs {a, b} that EVERY route
system of EVERY T-join must contain (ab a forced J-edge whose other edges at a and b are forced
out of J), and test whether the bad half-set M contains such a pair. If it does, M is never a
transversal of a pairing produced by Theorem 21, whatever tree and F^v-pairings are chosen."""
import networkx as nx

bad = {}
for line in open('manuscripts/missing-move/scripts/outputs/emm_counterexamples12_cut_test.log'):
    if line.startswith('EMM-FAIL'):
        parts = line.split()
        g6 = parts[1]
        M = eval(line.split(' M ')[1])
        bad[g6] = set(M)
for g6, M in bad.items():
    G = nx.from_graph6_bytes(g6.encode())
    Ev = {v for v in G if G.degree(v) % 2 == 0}
    forced_in, forced_out = set(), set()
    for a, b in nx.bridges(G):
        H = G.copy(); H.remove_edge(a, b)
        side = nx.node_connected_component(H, a)
        (forced_in if len(side & Ev) % 2 else forced_out).add(frozenset((a, b)))
    forced_pairs = []
    for e in forced_in:
        a, b = tuple(e)
        others = [frozenset((x, y)) for x in (a, b) for y in G[x] if y not in (a, b)]
        if all(o in forced_out for o in others):
            forced_pairs.append(tuple(sorted(e)))
    hit = [p for p in forced_pairs if set(p) <= M]
    print(g6, 'M', sorted(M), 'forced pairs', sorted(forced_pairs), '-> M contains forced pair:', hit)

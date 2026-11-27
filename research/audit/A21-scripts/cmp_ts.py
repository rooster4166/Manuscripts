"""cmp_ts.py -- audit A21: compare ts (no memo) with ts2 (frontier memo) on a random sample of the
first K order-9 graphs with one even vertex, on all T queries and on S/A queries of the kinds used.

usage: python3 cmp_ts.py K SAMPLE SEED"""
import sys, os, random, subprocess, itertools
import networkx as nx
from exhaust import Solver

HERE = os.path.dirname(os.path.abspath(__file__))
K, SAMPLE, SEED = map(int, sys.argv[1:4])
A, B = Solver(os.path.join(HERE, "ts")), Solver(os.path.join(HERE, "ts2"))
gs = []
for line in subprocess.run(["nauty-geng", "-cq", "9"], capture_output=True, text=True).stdout.split():
    G = nx.from_graph6_bytes(line.encode())
    ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    if len(ev) == 1:
        gs.append((line, G, ev[0]))
    if len(gs) >= K:
        break
rng = random.Random(SEED)
nq = mism = 0
for line, G, z in rng.sample(gs, SAMPLE):
    qs = []
    for x in G:
        if G.degree(x) % 2:
            qs += [(G, f"T {x} {y}") for y in G[x]]
    for u in G[z]:
        K1 = G.copy(); K1.remove_edge(u, z); qs.append((K1, f"S 1 {u} {z}"))
        for w in set(G[u]) & set(G[z]):
            K3 = G.copy(); K3.remove_edges_from([(u, z), (u, w), (w, z)])
            qs += [(K3, f"S 2 {w} {u} {w} {z}"), (K3, f"A {w} 2 {u} {z}")]
    odd = [v for v in G if G.degree(v) % 2]
    for c, a in itertools.product(odd, odd):
        if a != c and not G.has_edge(a, c):
            qs.append((G, f"A {c} 1 {a}"))
    for H, q in qs:
        nq += 1
        ra, rb = A.ask(H, q), B.ask(H, q)
        if ra != rb:
            mism += 1
            print("MISMATCH", line, q, ra, rb, flush=True)
print(f"cmp_ts: graphs={SAMPLE} queries={nq} mismatches={mism}")

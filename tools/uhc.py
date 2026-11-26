"""Test UHC*: every 2-connected graph B of even order n, every set S of exactly e/2
even vertices: B has a decomposition into exactly n/2 paths with 2 ends on S,
0 on the other even vertices, and 1 at every odd vertex.

Prints counterexamples with flush; summary at the end.
Usage: python3 uhc.py graphs.g6 [--critical-only] [--start i --step s]
"""
import itertools
import sys
import networkx as nx
from faithful_descent import make_oracle
from pathnum import path_number

args = sys.argv[1:]
crit_only = "--critical-only" in args
start = int(args[args.index("--start") + 1]) if "--start" in args else 0
step = int(args[args.index("--step") + 1]) if "--step" in args else 1

tested = fails = 0
for idx, line in enumerate(open(args[0])):
    if idx % step != start:
        continue
    G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(line.strip().encode()))
    n = G.number_of_nodes()
    if n % 2 or n < 3 or nx.node_connectivity(G) < 2:
        continue
    E, O, real = make_oracle(G)
    e = len(E)
    if e == 0:
        continue
    if crit_only and path_number(G) != n // 2:
        continue
    tested += 1
    bad = [sorted(S) for S in itertools.combinations(E, e // 2) if not real(frozenset(S))]
    if bad:
        fails += 1
        print("UHC-FAIL", line.strip(), "kappa", nx.node_connectivity(G), "E", E,
              "p", path_number(G), "bad halves", bad[:6], flush=True)
    if tested % 200 == 0:
        print(f"progress: tested {tested}, fails {fails}", flush=True)
print(f"DONE tested {tested} 2-connected graphs with even vertices; UHC* failures {fails}", flush=True)

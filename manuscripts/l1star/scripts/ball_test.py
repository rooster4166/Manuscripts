"""Exhaustive tests of region forms of L1* (l1star session), via the oracle l1s (mode ed).
For G with at most one even vertex g and an odd vertex c, test whether some Lovász decomposition
has V(Q_c) inside the region R:
  loc   : N[c] u N(g)                              (local form, Conjecture 1.4)
  ball  : B_2(c), the ball of radius 2             (route-descent's BALL / GL)
  inter : N[c] u (N(g) & B_2(c))                   (both at once)
  leaf  : only for c of degree 1 with neighbour y: {c} u N[y]   (route-descent's GL at a leaf)
usage: nauty-geng -cq n | python3 ball_test.py
"""
import sys, subprocess, os, collections
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
p = subprocess.Popen([os.path.join(HERE, "l1s"), "ed", "0"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
def q(G, c, R):
    E = list(G.edges())
    mask = sum(1 << v for v in G if v not in R and G.degree(v) > 0)
    p.stdin.write(f"{G.number_of_nodes()} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + f" {c} {mask}\n")
    p.stdin.flush()
    return int(p.stdout.readline())
C = collections.Counter(); ex = collections.defaultdict(list)
for line in sys.stdin:
    G = nx.from_graph6_bytes(line.strip().encode())
    ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    if len(ev) > 1: continue
    g = ev[0] if ev else None
    Ng = set(G[g]) if g is not None else set()
    for c in G:
        if G.degree(c) % 2 == 0: continue
        Nc = set(G[c]) | {c}
        B2 = set(Nc)
        for v in G[c]: B2 |= set(G[v])
        regions = {"ball": B2, "inter": Nc | (Ng & B2)}
        if G.degree(c) == 1:
            (y,) = list(G[c])
            regions["leaf"] = {c} | set(G[y]) | {y}
        for name, R in regions.items():
            r = q(G, c, R)
            key = name + (" one-even" if g is not None else " all-odd")
            C[key + " tests"] += 1
            if r != 1:
                C[key + " FAIL"] += 1
                if len(ex[key]) < 5: ex[key].append((line.strip(), g, c))
for k, v in sorted(C.items()): print(k, v)
for k, v in ex.items(): print("EX", k, v)

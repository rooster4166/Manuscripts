"""Cross-check pee.c against tools/route_ext.c (independent code).
EE: uz terminal at u in K  <=>  K - uz has a Lovasz decomposition whose path at z avoids u (X query).
Away edges: xy terminal at x in G <=> leaf graph G - xy + leaf at y has a decomposition with the
leaf separated from x (S query), profile: x gets 0, leaf 1, others deg mod 2.
usage: python3 xcheck_route_ext.py ROUTE_EXT_BINARY  < graphs.g6"""
import sys, subprocess, os, random
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
R = subprocess.Popen([sys.argv[1]], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
P = subprocess.Popen([os.path.join(HERE, "pee"), "ed"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
def rq(s):
    R.stdin.write(s + "\n"); R.stdin.flush(); return int(R.stdout.readline())
def pq(G, x, y):
    E = list(G.edges()); P.stdin.write(f"{G.number_of_nodes()} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + f" {x} {y}\n"); P.stdin.flush()
    return int(P.stdout.readline())
rng = random.Random(5); n_ee = n_aw = dis = 0
for line in sys.stdin:
    G = nx.from_graph6_bytes(line.strip().encode())
    ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    if len(ev) != 1: continue
    z = ev[0]; n = G.number_of_nodes()
    for u in G[z]:
        if G.degree(u) < 3: continue
        H = G.copy(); H.remove_edge(u, z); E = list(H.edges())
        b = [H.degree(v) % 2 for v in range(n)]
        r1 = rq(f"X {n} {len(E)} " + " ".join(f"{a} {c}" for a, c in E) + " " + " ".join(map(str, b)) + f" {z} {1 << u}")
        r2 = pq(G, u, z); n_ee += 1
        if r1 != r2: dis += 1; print("DIS-EE", line.strip(), z, u, r1, r2)
    arcs = [(x, y) for x in G for y in G[x] if x != z and y != z and G.degree(x) >= 3]
    for x, y in rng.sample(arcs, min(4, len(arcs))):
        H = G.copy(); H.remove_edge(x, y); l = n; H.add_edge(y, l); E = list(H.edges())
        b = [G.degree(v) % 2 for v in range(n)] + [1]; b[x] = 0
        r1 = rq(f"S {n+1} {len(E)} " + " ".join(f"{a} {c}" for a, c in E) + " " + " ".join(map(str, b)) + f" 1 {x} {l}")
        r2 = pq(G, x, y); n_aw += 1
        if r1 != r2: dis += 1; print("DIS-AW", line.strip(), z, x, y, r1, r2)
print(f"EE queries {n_ee}, away queries {n_aw}, disagreements {dis}")

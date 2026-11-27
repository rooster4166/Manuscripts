"""Triangle lemma, stronger form: in K - {uz,uw,zw}, separate w from u and from z (u, z may share a path)."""
import sys, subprocess, os, collections
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
P = subprocess.Popen([os.path.join(HERE, "pee3"), "edq", "0"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
def q(G, T, a, b):
    E = list(G.edges())
    P.stdin.write(f"{G.number_of_nodes()} {len(E)} " + " ".join(f"{x} {y}" for x, y in E) + f" {T} {a} {b}\n"); P.stdin.flush()
    return int(P.stdout.readline())
C = collections.Counter()
for line in sys.stdin:
    G = nx.from_graph6_bytes(line.strip().encode())
    ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    if len(ev) != 1: continue
    z = ev[0]
    for u in G[z]:
        T = set(G[u]) & set(G[z])
        for w in T:
            H = G.copy(); H.remove_edges_from([(u, z), (u, w), (z, w)])
            r = q(H, 3, w, (1 << u) | (1 << z))
            C[(len(T) >= 2, r)] += 1
print(dict(C))

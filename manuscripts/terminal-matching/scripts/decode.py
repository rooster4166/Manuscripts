"""decode.py: canonical H (g6 lines) -> 'g6(G - F) a1 b1 a2 b2 ...' lines for ptm mode f."""
import sys
import networkx as nx
for line in sys.stdin:
    s = line.strip()
    if not s: continue
    H = nx.from_graph6_bytes(s.encode())
    S = [v for v in H if H.degree(v) == 4]
    drop = set(S); pairs = []
    for v in S:
        nb = sorted(H[v], key=lambda w: H.degree(w))
        leaves, ends = nb[:2], nb[2:]
        drop |= set(leaves); pairs.append(ends)
    keep = sorted(set(H) - drop); idx = {v: i for i, v in enumerate(keep)}
    Gp = nx.Graph(); Gp.add_nodes_from(range(len(keep)))
    Gp.add_edges_from((idx[u], idx[w]) for u, w in H.edges() if u in idx and w in idx)
    print(nx.to_graph6_bytes(Gp, header=False).decode().strip(),
          ' '.join(f'{idx[a]} {idx[b]}' for a, b in pairs))

"""Audit A22c: frequency of far-apart N(z) at order n, own generator vs networkx's configuration
model (as in d6_reach.py), both filtered by the same 3-connectivity test; far test done both by
own code and by networkx distances."""
import sys, random, itertools
import networkx as nx
from far_check import rand_J, three_conn
n, count, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
def far_own(adj):
    Nz = sorted(adj[0]); H = [set(a) - {0} for a in adj]
    return not any(v in H[u] or H[u] & H[v] for u, v in itertools.combinations(Nz, 2))
def far_nx(adj):
    G = nx.Graph(); G.add_nodes_from(range(len(adj)))
    for u in range(len(adj)):
        for w in adj[u]: G.add_edge(u, w)
    Nz = sorted(G[0]); H = G.copy(); H.remove_node(0)
    d = {u: nx.single_source_shortest_path_length(H, u, cutoff=2) for u in Nz}
    return not any(v in d[u] for u, v in itertools.combinations(Nz, 2))
a = b = mism = 0
for _ in range(count):
    adj = rand_J(n, rng)
    fo, fn = far_own(adj), far_nx(adj); a += fo; mism += fo != fn
made = 0
while made < count:
    degs = [6] + [rng.choice((3, 3, 3, 5)) for _ in range(n - 1)]
    if sum(degs) % 2: continue
    G = nx.Graph(nx.configuration_model(degs, seed=rng.randrange(1 << 30)))
    G.remove_edges_from(nx.selfloop_edges(G))
    if [G.degree(v) for v in range(n)] != degs: continue
    adj = [set(G[v]) for v in range(n)]
    if not three_conn(n, adj): continue
    made += 1; b += far_own(adj)
print(f'n={n}: own generator far {a}/{count} (own vs nx far-test mismatches {mism}); nx configuration_model far {b}/{count}')

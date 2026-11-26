import sys, time, random, networkx as nx
from thm11_constr import run_case, pair_classes, min_path_cover
from wu_circ_lib import edge_graphs
n = int(sys.argv[1]); only_g = int(sys.argv[2]); k = (n - 1) // 2; rng = random.Random(2)
tally = {}; t0 = time.time()
for m in range(k):
    L = k - m
    Hs = [nx.empty_graph(n)] if m == 0 else []
    for X in (edge_graphs(m) if m > 0 else []):
        X = nx.convert_node_labels_to_integers(X); H = nx.empty_graph(n); H.add_edges_from(X.edges()); Hs.append(H)
    for H in Hs:
        for S in pair_classes(n, H, L + 1):
            G = nx.complete_graph(n); G.remove_edges_from(H.edges())
            g = len(min_path_cover(G.subgraph(S), S)) - 1
            if g < only_g: continue
            kind, gg, res = run_case(n, H, S, rng)
            tally[(kind, gg, res)] = tally.get((kind, gg, res), 0) + 1
            if res != "OK": print("NOT OK", n, sorted(H.edges()), S, kind, res, flush=True)
print(f"n={n} (only g>={only_g}): {tally}  {time.time()-t0:.0f}s", flush=True)

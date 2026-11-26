import sys, itertools
from common import *

def support_subgraphs(n, s, mmin):
    """All graphs H with >= mmin edges whose support has <= s vertices (up to iso), on vertex set range(n)."""
    out = []
    E = list(itertools.combinations(range(s), 2))
    buckets = {}
    for m in range(mmin, len(E) + 1):
        for es in itertools.combinations(E, m):
            H = nx.Graph(); H.add_nodes_from(range(n)); H.add_edges_from(es)
            key = nx.weisfeiler_lehman_graph_hash(H, iterations=3)
            lst = buckets.setdefault(key, [])
            if any(nx.is_isomorphic(H, K) for K in lst): continue
            lst.append(H); out.append(H)
    return out

for k in (2, 3):
    n = 2 * k + 1
    # m = k
    res = []
    for H in iso_classes_edge_sets(n, k):
        G = complement_of(n, H)
        r = solve(G)
        assert r.status == "OPTIMAL" and verify_partition(G, r.paths)
        res.append(r.value == k and all(len(P) == n for P in r.paths))
    print(f"k={k} m=k: {len(res)} classes, all p=k with Hamilton paths: {all(res)}")
    # m > k, support <= k+1
    res = []
    for H in support_subgraphs(n, k + 1, k + 1):
        G = complement_of(n, H)
        r = solve(G)
        assert r.status == "OPTIMAL" and verify_partition(G, r.paths)
        res.append((H.number_of_edges(), r.value))
    print(f"k={k} m>k support<=k+1: {len(res)} classes, values {sorted(set(res))}, all p=k: {all(v == k for _, v in res)}")
    # sharpness of total L+1: m-matching, L+2 universal vertices with r=1 each
    for m in range(0, k):
        L = k - m
        H = nx.Graph(); H.add_nodes_from(range(n)); H.add_edges_from((2 * i, 2 * i + 1) for i in range(m))
        G = complement_of(n, H)
        univ = list(range(2 * m, n))[:L + 2]
        r = solve(G, budget=k + 1, min_ends={v: 1 for v in univ})
        print(f"k={k} m={m}: matching + {L+2} universal vertices each >=1 end within k+1 paths: {r.status}")
        # and with L+1 of them it is feasible
        r2 = solve(G, budget=k + 1, min_ends={v: 1 for v in univ[:L + 1]})
        print(f"   with {L+1} universal vertices: {r2.status} value {r2.value}")

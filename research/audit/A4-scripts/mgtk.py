"""Theorem 4, last sentence: m > k and H supported on <= k+1 vertices => p(K_{2k+1}-H) = k.
Replay: split H into exactly k nonempty paths, find a Hamilton decomposition with path i inside cycle i (CP-SAT),
remove the paths, verify the k resulting paths partition K_n - H."""
import itertools, sys, time, networkx as nx
from circ import ham_decomp, check
def k_path_split(H, k):
    import random
    rng = random.Random(0)
    for trial in range(20000):
        R = nx.Graph(H.edges()); paths = []
        while R.number_of_edges():
            v = rng.choice([u for u in R if R.degree(u) > 0]); P = [v]
            while True:
                nb = [w for w in R[P[-1]] if w not in P]
                if not nb: break
                w = rng.choice(nb); R.remove_edge(P[-1], w); P.append(w)
            R.remove_nodes_from([u for u in list(R) if R.degree(u) == 0])
            paths.append(P)
        if len(paths) > k: continue
        while len(paths) < k:
            paths.sort(key=len); P = paths.pop(); i = len(P) // 2
            paths += [P[:i+1], P[i:]]
            if any(len(p) < 2 for p in paths): break
        if len(paths) == k and all(len(p) >= 2 for p in paths):
            return [[(p[i], p[i+1]) for i in range(len(p)-1)] for p in paths]
    return None
def order_path(es):
    G = nx.Graph(es); ends = [v for v in G if G.degree(v) == 1]
    return nx.shortest_path(G, ends[0], ends[1])
for k in [int(a) for a in sys.argv[1:]]:
    n = 2 * k + 1; s = k + 1; t0 = time.time()
    E = list(itertools.combinations(range(s), 2)); seen = []; ok = tot = 0
    for m in range(k + 1, len(E) + 1):
        for es in itertools.combinations(E, m):
            H = nx.Graph(es)
            if any(nx.is_isomorphic(H, K) for K in seen): continue
            seen.append(H); tot += 1
            cls = k_path_split(H, k)
            st, cyc = ham_decomp(n, cls, time_limit=600)
            good = cyc is not None and check(n, cyc, cls)
            if good:
                G = nx.complete_graph(n); G.remove_edges_from(H.edges()); used = set(); paths = []
                for c in range(k):
                    cy = cyc[c]; ce = [frozenset((cy[i], cy[(i+1) % n])) for i in range(n)]
                    rest = [tuple(e) for e in ce if e not in {frozenset(f) for f in cls[c]}]
                    P = order_path(rest)
                    for a, b in zip(P, P[1:]):
                        f = frozenset((a, b)); assert G.has_edge(a, b) and f not in used; used.add(f)
                    paths.append(P)
                good = len(used) == G.number_of_edges()
            ok += good
            if not good: print("FAIL", k, es, st, flush=True)
    print(f"k={k} (n={n}): m>k, support<=k+1: {ok}/{tot} classes give k-path partitions of K_n - H; {time.time()-t0:.0f}s", flush=True)

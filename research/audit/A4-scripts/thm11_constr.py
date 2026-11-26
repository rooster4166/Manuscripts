"""Replay the construction of Theorem 11 / Corollary 12 (odd-semi-clique-boundary) at small odd n,
with the Hamilton decomposition step found by CP-SAT (not assumed), then verify the resulting
(k+1)-path partition, its endpoint vector d_H + 2*1_S and its end-pair multigraph H + C."""
import itertools, sys, time, random
import networkx as nx
from circ import ham_decomp, check
from common import iso_classes_edge_sets

def min_path_cover(Gs, S):
    """Minimum vertex-disjoint path cover of G[S] (brute force over orderings), returns list of paths."""
    S = list(S); best = None
    for perm in itertools.permutations(S):
        paths = [[perm[0]]]
        for v in perm[1:]:
            if Gs.has_edge(paths[-1][-1], v): paths[-1].append(v)
            else: paths.append([v])
        if best is None or len(paths) < len(best):
            best = paths
            if len(best) == 1: break
    return best

def build(n, H, S, rng):
    k = (n - 1) // 2; m = H.number_of_edges(); L = k - m
    G = nx.complete_graph(n); G.remove_edges_from(H.edges())
    dH = dict(H.degree()); Sset = set(S)
    univ = [v for v in range(n) if dH.get(v, 0) == 0 and v not in Sset]
    cover = min_path_cover(G.subgraph(S), S); g = len(cover) - 1
    Hedges = [tuple(e) for e in H.edges()]
    if g == 0:
        Q = cover[0]
        classes = [[e] for e in Hedges] + [[(Q[i], Q[i + 1])] for i in range(len(Q) - 1)]
        return dict(kind="g0", G=G, k=k, L=L, g=g, Q=Q, classes=classes, W=[])
    if L == 1:
        a, b = S
        pad = rng.choice([tuple(e) for e in G.edges()])
        classes = [[e] for e in Hedges] + [[pad]]
        return dict(kind="L1", G=G, k=k, L=L, g=g, classes=classes, S=(a, b))
    if g == 1 and L == 2:
        # S = {a,b,c}, ab the only surviving edge
        two = [p for p in cover if len(p) == 2][0]; a, b = two; c = [v for v in S if v not in two][0]
        pad = rng.choice([tuple(e) for e in G.edges() if set(e) != {a, b}])
        classes = [[e] for e in Hedges] + [[(a, b)], [pad]]
        return dict(kind="g1L2", G=G, k=k, L=L, g=g, classes=classes, abc=(a, b, c))
    W = univ[:g]
    assert len(W) == g
    Q = []
    for i, p in enumerate(cover):
        Q += p
        if i < g: Q.append(W[i])
    wedge_edges = set()
    classes = [[e] for e in Hedges]
    for w in W:
        i = Q.index(w); classes.append([(Q[i - 1], w), (w, Q[i + 1])])
        wedge_edges |= {frozenset((Q[i - 1], w)), frozenset((w, Q[i + 1]))}
    for i in range(len(Q) - 1):
        if frozenset((Q[i], Q[i + 1])) not in wedge_edges: classes.append([(Q[i], Q[i + 1])])
    assert len(classes) == k, (len(classes), k)
    return dict(kind="general", G=G, k=k, L=L, g=g, Q=Q, classes=classes, W=W)

def open_cycle(cyc, cl):
    n = len(cyc)
    if len(cl) == 1:
        u, v = cl[0]; i = cyc.index(u)
        if cyc[(i + 1) % n] == v: return [cyc[(i + 1 + j) % n] for j in range(n)]
        return [cyc[(i - 1 - j) % n] for j in range(n)]  # starts at v ... ends at u
    (a, w), (w2, b) = cl; assert w == w2
    i = cyc.index(w)
    rot = [cyc[(i + 1 + j) % n] for j in range(n - 1)]  # path omitting w
    return rot

def arcs_between(cyc, x, y):
    n = len(cyc); i = cyc.index(x); j = cyc.index(y)
    a1 = [cyc[(i + t) % n] for t in range((j - i) % n + 1)]
    a2 = [cyc[(i - t) % n] for t in range((i - j) % n + 1)]
    return a1, a2

def verify(n, H, S, G, paths):
    seen = set()
    for P in paths:
        assert len(P) >= 2 and len(set(P)) == len(P)
        for a, b in zip(P, P[1:]):
            e = frozenset((a, b)); assert G.has_edge(a, b) and e not in seen; seen.add(e)
    assert len(seen) == G.number_of_edges()
    k = (n - 1) // 2; assert len(paths) == k + 1
    dH = dict(H.degree()); ends = {v: 0 for v in range(n)}
    pairs = {}
    for P in paths:
        ends[P[0]] += 1; ends[P[-1]] += 1
        pr = frozenset((P[0], P[-1])); pairs[pr] = pairs.get(pr, 0) + 1
    want = {v: dH.get(v, 0) + (2 if v in S else 0) for v in range(n)}
    assert ends == want, (ends, want)
    # Corollary 12: pairs minus H must be a single cycle on S (2 parallel edges if |S|=2)
    rest = dict(pairs)
    for e in H.edges():
        f = frozenset(e); rest[f] -= 1; assert rest[f] >= 0
    rest = {e: c for e, c in rest.items() if c}
    M = nx.MultiGraph(); M.add_nodes_from(S)
    for e, c in rest.items():
        for _ in range(c): M.add_edge(*tuple(e))
    assert set(M.nodes()) == set(S)
    assert all(d == 2 for _, d in M.degree()) and nx.is_connected(M) and M.number_of_edges() == len(S)
    return True

def run_case(n, H, S, rng, tl=900):
    B = build(n, H, S, rng); k = B["k"]
    st, cyc = ham_decomp(n, B["classes"], time_limit=tl, seed=rng.randrange(1000))
    if cyc is None: return B["kind"], B["g"], st
    check(n, cyc, B["classes"])
    kind = B["kind"]
    if kind in ("g0", "general"):
        paths = [open_cycle(cyc[c], B["classes"][c]) for c in range(k)] + [B["Q"]]
    elif kind == "L1":
        a, b = B["S"]; paths = [open_cycle(cyc[c], B["classes"][c]) for c in range(k - 1)]
        paths += list(arcs_between(cyc[k - 1], a, b))
    else:
        a, b, c0 = B["abc"]; paths = [open_cycle(cyc[c], B["classes"][c]) for c in range(k - 1)]
        a1, a2 = arcs_between(cyc[k - 1], c0, a)
        if b in a1: a1, a2 = a2, a1
        paths += [a1 + [b], a2]
    verify(n, H, S, B["G"], paths)
    return kind, B["g"], "OK"

def pair_classes(n, H, size):
    out = []; buckets = {}
    for S in itertools.combinations(range(n), size):
        K = H.copy(); nx.set_node_attributes(K, {v: (v in S) for v in range(n)}, "s")
        key = nx.weisfeiler_lehman_graph_hash(K, node_attr="s", iterations=3)
        lst = buckets.setdefault(key, [])
        nm = nx.algorithms.isomorphism.categorical_node_match("s", None)
        if any(nx.is_isomorphic(K, K2, node_match=nm) for K2 in lst): continue
        lst.append(K); out.append(S)
    return out

if __name__ == "__main__":
    n = int(sys.argv[1]); only_g = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    k = (n - 1) // 2; rng = random.Random(1)
    tally = {}
    t0 = time.time()
    for m in range(k):
        L = k - m
        for H in iso_classes_edge_sets(n, m):
            for S in pair_classes(n, H, L + 1):
                G = nx.complete_graph(n); G.remove_edges_from(H.edges())
                g = len(min_path_cover(G.subgraph(S), S)) - 1
                if g < only_g: continue
                kind, gg, res = run_case(n, H, S, rng)
                tally.setdefault((kind, res), 0); tally[(kind, res)] += 1
                if res != "OK": print("NOT OK", n, sorted(H.edges()), S, kind, res, flush=True)
    print(f"n={n} (only g>={only_g}): {tally}  {time.time()-t0:.0f}s", flush=True)

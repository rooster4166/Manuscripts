"""End-to-end test of the repaired proof of Theorem 8 (Theorem A in the manuscript):
 1. random instance (P on K_r, G rainbow in P_1..P_t, size conditions, r <= 2t-1);
 2. repeat the two-vertex step: integral flow in the Stage-Z network (networkx),
    then the split by a proper 2-edge-colouring of a max-degree-2 bipartite graph;
 3. complete by Hilton one-vertex steps (CP-SAT) and close the cycles;
 4. verify: n Hamilton cycles of K_{2n+1}, P_i subset C_i, G + matching rainbow."""
import random, sys
import networkx as nx
from lf import components, edges_by_colour, is_linear_forest, pvec, tvl_demands
from solvers import one_vertex_step

def stageZ_record(m, n, col, U, c):
    K = 2 * n + 1 - m
    p = pvec(m, n, col); d = tvl_demands(p, K, U, c)
    E = edges_by_colour(m, n, col)
    comps = [components(m, E[i]) for i in range(n)]
    G = nx.DiGraph(); excess = {}
    def arc(a, b, lo, hi):
        if hi > lo: G.add_edge(a, b, capacity=hi - lo)
        if lo:
            excess[b] = excess.get(b, 0) + lo; excess[a] = excess.get(a, 0) - lo
        lower[(a, b)] = lo
    lower = {}
    for v in range(m): arc("s", ("v", v), 2, 2)
    for i in range(n):
        for k, (u, w) in enumerate(comps[i]):
            C = ("C", i, k)
            if u == w: arc(("v", u), C, 0, 2)
            else: arc(("v", u), C, 0, 1); arc(("v", w), C, 0, 1)
            arc(C, ("g", i), 0, 1); arc(C, ("h", i), 0, 1)
        if i != c: arc(("h", i), ("g", i), 0, 1)
        arc(("g", i), "t", d[i], 2 if i == c else 4)
    G.add_edge("t", "s", capacity=10**6)
    need = 0
    for node, e in excess.items():
        if e > 0: G.add_edge("SS", node, capacity=e); need += e
        elif e < 0: G.add_edge(node, "TT", capacity=-e)
    val, F = nx.maximum_flow(G, "SS", "TT")
    if val != need: return None
    # attachments: a[(v,i,k)] = flow on v -> C(i,k)
    att = []
    for i in range(n):
        for k, (u, w) in enumerate(comps[i]):
            C = ("C", i, k)
            for v in {u, w}:
                f = F.get(("v", v), {}).get(C, 0)
                att += [(v, i, k)] * f
    return att, comps

def split(m, n, att, comps, c):
    """Proper 2-edge-colouring of the bipartite multigraph F* (max degree 2)."""
    # build sub-nodes for colours
    by_col = {}
    for idx, (v, i, k) in enumerate(att):
        by_col.setdefault(i, []).append(idx)
    sub = {}
    for i, L in by_col.items():
        cnt = {}
        for idx in L: cnt[att[idx][2]] = cnt.get(att[idx][2], 0) + 1
        dbl = [k for k, x in cnt.items() if x == 2]
        assert len(dbl) <= (0 if i == c else 1)
        pair = [idx for idx in L if dbl and att[idx][2] == dbl[0]]
        rest = [idx for idx in L if idx not in pair]
        groups = ([pair] if pair else []) + [rest[j:j + 2] for j in range(0, len(rest), 2)]
        assert len(groups) <= (1 if i == c else 2) and all(len(g) <= 2 for g in groups)
        for gi, g in enumerate(groups):
            for idx in g: sub[idx] = ("col", i, gi)
    # graph: nodes vertex v, sub-node; edges = attachments; max degree 2
    H = nx.MultiGraph()
    for idx, (v, i, k) in enumerate(att):
        H.add_edge(("v", v), sub[idx], key=idx)
    lab = {}
    for comp in nx.connected_components(H):
        S = H.subgraph(comp)
        # walk an Euler-like trail: path or cycle, alternate labels
        ends = [x for x in S.nodes if S.degree(x) == 1]
        start = ends[0] if ends else next(iter(S.nodes))
        prev_key, cur, l = None, start, 0
        used = set()
        while True:
            nxt = [(a, b, key) for a, b, key in S.edges(cur, keys=True) if key not in used]
            if not nxt: break
            a, b, key = nxt[0]; used.add(key); lab[key] = l; l ^= 1
            cur = b if a == cur else a
        assert len(used) == S.number_of_edges()
    return lab

def tvl_step(m, n, col, U, c):
    rec = stageZ_record(m, n, col, U, c)
    assert rec is not None, "flow infeasible"
    att, comps = rec
    lab = split(m, n, att, comps, c)
    new = dict(col); x, y = m, m + 1
    for idx, (v, i, k) in enumerate(att):
        new[(v, x if lab[idx] == 0 else y)] = i
    new[(x, y)] = c
    E2 = edges_by_colour(m + 2, n, new)
    assert len(new) == (m + 2) * (m + 1) // 2
    assert all(is_linear_forest(m + 2, E2[i]) for i in range(n))
    K = 2 * n + 1 - m
    p2 = [m + 2 - len(E2[i]) for i in range(n)]
    for i in range(n):
        assert p2[i] <= (K - 3 if (i in U and i != c) else K - 2)
    return new

def random_instance(rng, nmax=9):
    while True:
        n = rng.randint(4, nmax)
        t = rng.randint(2, n - 1)
        r = rng.randint(2, min(2 * t - 1, 2 * n))
        col = {}
        for mm in range(1, r):
            col = one_vertex_step(mm, n, col, rng)
        K0 = 2 * n + 1 - r
        p = pvec(r, n, col); E = edges_by_colour(r, n, col)
        Ucand = [i for i in range(n) if p[i] <= K0 - 1]
        if len(Ucand) < n - t: continue
        rng.shuffle(Ucand); Ucand.sort(key=lambda i: -p[i])
        U = Ucand[:n - t]; T = [i for i in range(n) if i not in U]
        if any(len(E[i]) == 0 for i in T): continue
        Gedges = {i: rng.choice(E[i]) for i in T}
        return n, t, r, col, T, U, Gedges

def run(seed, trials):
    rng = random.Random(seed)
    for tr in range(trials):
        n, t, r, col, T, U, Gedges = random_instance(rng)
        m = r; Uset = set(U); matching = {}
        order = list(U); rng.shuffle(order)
        for c in order:
            col = tvl_step(m, n, col, Uset, c)
            matching[c] = (m, m + 1); Uset.discard(c); m += 2
        while m < 2 * n:
            col = one_vertex_step(m, n, col, rng); m += 1
        # close: vertex 2n joined to the two ends of each Hamilton path
        E = edges_by_colour(m, n, col)
        for i in range(n):
            comps = components(m, E[i]); assert len(comps) == 1
            u, w = comps[0]; col[(u, m)] = i; col[(w, m)] = i
        N = 2 * n + 1
        assert len(col) == N * (N - 1) // 2
        E = edges_by_colour(N, n, col)
        for i in range(n):
            g = nx.Graph(E[i]); assert g.number_of_nodes() == N and all(dg == 2 for _, dg in g.degree()) and nx.is_connected(g)
        rainbow = {}
        for i, e in Gedges.items(): rainbow[e] = i
        for i, e in matching.items(): rainbow[e] = i
        assert all(col[e] == i for e, i in rainbow.items()) and len(set(rainbow.values())) == n
        print("ok n=%d t=%d r=%d" % (n, t, r))
if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]))

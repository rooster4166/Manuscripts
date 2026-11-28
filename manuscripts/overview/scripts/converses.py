"""Independent brute-force check of the three converses proved in the overview (Props 3.8, 3.11, 3.13):
  (A) all-odd (T1) lift:  base on H = (J-z) - Phi  <=>  J - z has <= k paths, Phi terminal at parents;
  (B) (T2) forest lift:   base on M = J - zT - Phi <=>  the leaf graph J - zT has <= |J|/2 paths,
                          Phi terminal at parents;
  (C) floor lift:         base on B - Phi          <=>  B = J - z has <= (|B|-1)/2 paths, Phi terminal.
A base is a parity decomposition (ends(v) = deg(v) mod 2) with (i) p(v) not on the path ending at
v, (ii) siblings end different paths.  Everything is enumerated exhaustively (no caps): every
decomposition of the graph with at most the allowed number of paths, every forest T-join Phi
(every edge subset), every admissible rooting.  Also checks that every lifted decomposition passes
the test.  Self-contained: uses only networkx for the graph atlas and random graphs.
usage: python3 converses.py [seed] [samples8]
"""
import itertools, random, sys
import networkx as nx

def paths_through(adj, used, e):
    """All simple paths (vertex lists) using unused edges and containing edge e=(a,b)."""
    a, b = e
    res = []
    def ext(path, onp, side_done):
        # extend at the right end; when right extension stops, optionally extend at the left
        res.append(list(path))
        u = path[-1]
        for x in adj[u]:
            f = frozenset((u, x))
            if f in used or x in onp: continue
            used.add(f); onp.add(x); path.append(x)
            ext(path, onp, side_done)
            path.pop(); onp.discard(x); used.discard(f)
    # enumerate as: left part (reversed) + [a,b] + right part; to avoid duplicates generate
    # all simple paths containing ab by growing both sides independently
    out = set()
    def grow_left(path, onp):
        # path starts at its left end; grow right
        def grow_right(p, onp2):
            out.add(tuple(p) if p[0] <= p[-1] else tuple(reversed(p)))
            u = p[-1]
            for x in adj[u]:
                f = frozenset((u, x))
                if f in used or x in onp2: continue
                used.add(f); onp2.add(x); p.append(x)
                grow_right(p, onp2)
                p.pop(); onp2.discard(x); used.discard(f)
        grow_right(list(path), set(onp))
        u = path[0]
        for x in adj[u]:
            f = frozenset((u, x))
            if f in used or x in onp: continue
            used.add(f); onp.add(x)
            grow_left([x] + path, onp)
            onp.discard(x); used.discard(f)
    used.add(frozenset((a, b)))
    grow_left([a, b], {a, b})
    used.discard(frozenset((a, b)))
    return [list(p) for p in out]

def decomps(G, maxp, ends_req=None):
    """All path decompositions of G with at most maxp paths (as lists of vertex lists).
    If ends_req is given (dict v -> required end count), only those with exactly these ends."""
    edges = sorted(tuple(sorted(e)) for e in G.edges())
    adj = {v: sorted(G.neighbors(v)) for v in G.nodes()}
    used = set(); out = []
    endc = {v: 0 for v in G.nodes()}
    def rec(paths):
        if len(paths) > maxp: return
        rest = [e for e in edges if frozenset(e) not in used]
        if not rest:
            if ends_req is None or all(endc[v] == ends_req[v] for v in G.nodes()):
                out.append([list(p) for p in paths])
            return
        if len(paths) == maxp: return
        e = rest[0]
        for p in paths_through(adj, used, e):
            fs = [frozenset((p[i], p[i+1])) for i in range(len(p)-1)]
            if ends_req is not None and (endc[p[0]] + 1 > ends_req[p[0]] or endc[p[-1]] + 1 > ends_req[p[-1]]):
                continue
            for f in fs: used.add(f)
            endc[p[0]] += 1; endc[p[-1]] += 1
            paths.append(p); rec(paths); paths.pop()
            endc[p[0]] -= 1; endc[p[-1]] -= 1
            for f in fs: used.discard(f)
    rec([])
    return out

def ends_of(paths, v):
    return sum((p[0] == v) + (p[-1] == v) for p in paths)

def is_forest(Fe):
    F = nx.Graph(); F.add_edges_from(Fe)
    return nx.is_forest(F) if F.number_of_edges() else True

def tjoin_forests(B, T):
    """All forests Phi of B (edge subsets) whose odd-degree vertices are exactly T."""
    E = list(B.edges()); res = []
    for m in range(0, len(E) + 1):
        for S in itertools.combinations(E, m):
            deg = {}
            for a, b in S:
                deg[a] = deg.get(a, 0) + 1; deg[b] = deg.get(b, 0) + 1
            if {v for v, d in deg.items() if d % 2} != set(T): continue
            if is_forest(S): res.append(list(S))
    return res

def rootings(Phi, must_root=None, never_child=None):
    """All rootings of the forest Phi: list of parent maps child -> parent."""
    F = nx.Graph(); F.add_edges_from(Phi)
    comps = [sorted(c) for c in nx.connected_components(F)]
    choices = []
    for c in comps:
        opts = c
        if must_root is not None and must_root in c: opts = [must_root]
        if never_child is not None and never_child in c: opts = [never_child]
        choices.append(opts)
    for roots in itertools.product(*choices):
        par = {}
        for c, rt in zip(comps, roots):
            T = nx.bfs_tree(F.subgraph(c), rt)
            for u, v in T.edges(): par[v] = u
        yield par

def base_ok(paths, par):
    endpath = {}
    for i, p in enumerate(paths):
        for v in (p[0], p[-1]): endpath.setdefault(v, []).append(i)
    for v, pv in par.items():
        if len(endpath.get(v, [])) != 1: return False
        if pv in paths[endpath[v][0]]: return False
    kids = {}
    for v, pv in par.items(): kids.setdefault(pv, []).append(v)
    for pv, ks in kids.items():
        idx = [endpath[v][0] for v in ks]
        if len(set(idx)) != len(idx): return False
    return True

def terminal_ok(paths, par):
    for v, pv in par.items():
        ok = False
        for p in paths:
            if (p[0] == pv and p[1] == v) or (p[-1] == pv and p[-2] == v): ok = True
        if not ok: return False
    return True

def append_forest(paths, par):
    """Forest stepping: append p(v)v at the v-end of the path ending at v (parent-first order)."""
    P = [list(p) for p in paths]
    order = []  # children in parent-first order (BFS depth)
    depth = {}
    def d(v):
        if v not in par: return 0
        if v not in depth: depth[v] = 1 + d(par[v])
        return depth[v]
    for v in sorted(par, key=d):
        for p in P:
            if p[-1] == v: p.append(par[v]); break
            if p[0] == v: p.insert(0, par[v]); break
        else: return None
    return P

def is_decomp(G, paths):
    seen = set()
    for p in paths:
        if len(set(p)) != len(p) or len(p) < 2: return False
        for i in range(len(p)-1):
            f = frozenset((p[i], p[i+1]))
            if not G.has_edge(p[i], p[i+1]) or f in seen: return False
            seen.add(f)
    return len(seen) == G.number_of_edges()

stats = {k: [0, 0, 0, 0] for k in 'ABC'}  # instances, agreements, lift checks, positives
def check(tag, base_graph, full_graph, Phi, par, maxp_full, lift_test):
    st = stats[tag]
    L = decomps(base_graph, 10**9, {v: base_graph.degree(v) % 2 for v in base_graph.nodes()})
    a_witness = [D for D in L if base_ok(D, par)]
    a = bool(a_witness)
    F = decomps(full_graph, maxp_full)
    b = any(terminal_ok(D, par) for D in F)
    st[0] += 1; st[1] += (a == b); st[3] += a
    if a != b: print('MISMATCH', tag, sorted(full_graph.edges()), Phi, par, a, b, flush=True)
    for D in a_witness:
        D1 = append_forest(D, par)
        assert D1 is not None and is_decomp(full_graph, D1) and len(D1) <= maxp_full and terminal_ok(D1, par), (tag, D, par)
        assert lift_test(D1), (tag, D1)
        st[2] += 1

def run_graph(J):
    n = J.number_of_nodes()
    ev = [v for v in J if J.degree(v) % 2 == 0]
    if n % 2 == 1 and len(ev) == 1:          # (T1) all-odd lift
        z = ev[0]; B = J.copy(); B.remove_node(z); k = (n - 1) // 2
        if not nx.is_connected(B): return
        T = sorted(J.neighbors(z))
        H0 = B
        for Phi in tjoin_forests(B, T):
            for r in T:
                for par in rootings(Phi, must_root=r):
                    H = B.copy(); H.remove_edges_from(Phi)
                    check('A', H, B, Phi, par, k, lambda D1, r=r: ends_of(D1, r) >= 2)
    if n % 2 == 0 and len(ev) == 2 and J.has_edge(*ev):
        for z, r in (ev, ev[::-1]):
            if J.degree(r) < 3: continue
            B = J.copy(); B.remove_node(z)
            if not nx.is_connected(B): continue
            Nz = sorted(J.neighbors(z)); T = [v for v in Nz if v != r]
            G = J.copy(); G.remove_edges_from([(z, v) for v in T])   # leaf graph B + zr
            for Phi in tjoin_forests(B, Nz):                          # (B) (T2) forest lift
                for par in rootings(Phi):
                    kids_r = sum(1 for v in par if par[v] == r)
                    if r in par and kids_r < 2: continue
                    M = G.copy(); M.remove_edges_from(Phi)
                    check('B', M, G, Phi, par, n // 2,
                          lambda D1, r=r: ends_of(D1, r) >= 2)
            for w in T:                                               # (C) floor lift
                TT = [v for v in T if v != w]
                for Phi in tjoin_forests(B, TT):
                    for par in rootings(Phi, never_child=w):
                        H = B.copy(); H.remove_edges_from(Phi)
                        check('C', H, B, Phi, par, (B.number_of_nodes() - 1) // 2,
                              lambda D1: True)

def main():
  seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
  samples8 = int(sys.argv[2]) if len(sys.argv) > 2 else 0
  cnt = 0
  for J in nx.graph_atlas_g():
      if J.number_of_nodes() < 4 or not nx.is_connected(J): continue
      if J.number_of_edges() > 13: continue
      cnt += 1; run_graph(J)
  print('atlas graphs (connected, <= 7 vertices, <= 13 edges):', cnt, 'stats', stats, flush=True)
  rng = random.Random(seed); done = 0
  while done < samples8:
      J = nx.gnp_random_graph(8, rng.choice([0.35, 0.45, 0.55]), seed=rng.randrange(10**9))
      if not nx.is_connected(J) or J.number_of_edges() > 14: continue
      ev = [v for v in J if J.degree(v) % 2 == 0]
      if len(ev) != 2 or not J.has_edge(*ev): continue
      done += 1; run_graph(J)
  print('order-8 random samples:', samples8, 'FINAL', stats, flush=True)

if __name__ == '__main__':
  main()

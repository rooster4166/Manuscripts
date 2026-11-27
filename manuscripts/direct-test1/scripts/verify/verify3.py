"""Independent computational check of three forwarded claims (2026-11-27).

Claim 1 (forest edge-stepping): G even order, J a minimum T-join (T = Ev(G)), F = G - E(J).
  For every Lovasz decomposition Q0 of F and every rooting of the components of J, appending each
  parent edge (p(v), v) at the v-end of Q0(v) gives k simple paths partitioning E(G)
  IFF (i) p(v) not in V(Q0(v)) for all non-roots v, and (ii) Q0(x) != Q0(y) for siblings x != y.
Claim 2 (T-join lift to Test1): J 3-connected, z the only even vertex, d(z) = 2m; r, w in N(z);
  T = N(z) - {r, w}; J_T a minimum T-join of H = J - {z, r}; M = J - zw - {zv : v in T} - E(J_T).
  Parities of M as stated; and every Lovasz decomposition Q0 of M with (i),(ii) for a rooting of
  J_T (w's component rooted at w) lifts (delete z, then append parent edges) to a Test1
  decomposition of J - z.
Claim 3 (single pair, d(z) = 4): in M (J 2-connected) no component has odd set exactly {a1, b1};
  and test whether |C cap Odd(M)| >= 4 forces L1*-admissibility of a direction (Lean Admissible:
  a != c, a not adj c, a not adj any even vertex of M), and whether the OR holds.

Enumeration of Lovasz decompositions is exhaustive (capped; caps are reported).
"""
import itertools
import random
import sys

import networkx as nx

CAP = 4000


def lovasz_decomps(G, cap=CAP):
    """All path decompositions with ends(v) = deg(v) mod 2 (b <= 1), up to cap. Yields lists of
    vertex lists."""
    nodes = list(G.nodes())
    adj = {v: set(G.neighbors(v)) for v in nodes}
    used = set()
    rem = {v: G.degree(v) % 2 for v in nodes}
    deg = {v: G.degree(v) for v in nodes}
    out = []

    def feasible():
        for v in nodes:
            if rem[v] > deg[v] or (deg[v] - rem[v]) % 2:
                return False
        return True

    def rec(paths):
        if len(out) >= cap:
            return
        starts = [v for v in nodes if rem[v] > 0]
        if not starts:
            if all(deg[v] == 0 for v in nodes):
                out.append([list(p) for p in paths])
            return
        s = min(starts)
        # grow a path from s
        path = [s]
        onpath = {s}

        def grow():
            if len(out) >= cap:
                return
            u = path[-1]
            for x in sorted(adj[u]):
                e = frozenset((u, x))
                if e in used or x in onpath:
                    continue
                used.add(e); deg[u] -= 1; deg[x] -= 1
                path.append(x); onpath.add(x)
                if rem[x] > 0:  # option: stop here
                    rem[s] -= 1; rem[x] -= 1
                    if feasible():
                        paths.append(list(path))
                        rec(paths)
                        paths.pop()
                    rem[s] += 1; rem[x] += 1
                grow()
                path.pop(); onpath.discard(x)
                used.discard(e); deg[u] += 1; deg[x] += 1

        grow()

    rec([])
    return out


def end_map(paths):
    em = {}
    for i, P in enumerate(paths):
        for v in (P[0], P[-1]):
            em.setdefault(v, []).append(i)
    return em


def min_tjoin(G, T):
    """Minimum T-join via min-weight perfect matching on shortest-path distances."""
    T = list(T)
    if not T:
        return set()
    dist = dict(nx.all_pairs_shortest_path_length(G))
    K = nx.Graph()
    for a, b in itertools.combinations(T, 2):
        K.add_edge(a, b, weight=dist[a][b])
    mt = nx.min_weight_matching(K)
    J = set()
    for a, b in mt:
        p = nx.shortest_path(G, a, b)
        for x, y in zip(p, p[1:]):
            J ^= {frozenset((x, y))}
    return J


def rootings(Jedges, forced_root=None, maxr=6, rng=None):
    """Some rootings of the forest Jedges: dict v -> parent for non-roots."""
    F = nx.Graph([tuple(e) for e in Jedges])
    comps = [list(c) for c in nx.connected_components(F)]
    choices = []
    for c in comps:
        if forced_root is not None and forced_root in c:
            choices.append([forced_root])
        else:
            choices.append(sorted(c))
    allc = list(itertools.product(*choices))
    if rng is not None and len(allc) > maxr:
        allc = rng.sample(allc, maxr)
    res = []
    for roots in allc:
        par = {}
        for c, rt in zip(comps, roots):
            T = nx.bfs_tree(F.subgraph(c), rt)
            for u, v in T.edges():
                par[v] = u
        res.append(par)
    return res


def predicate(paths, par):
    em = end_map(paths)
    for v, p in par.items():
        if v not in em:
            return False
        if p in paths[em[v][0]]:
            return False
    kids = {}
    for v, p in par.items():
        kids.setdefault(p, []).append(v)
    for p, ks in kids.items():
        for x, y in itertools.combinations(ks, 2):
            if em[x][0] == em[y][0]:
                return False
    return True


def append_and_check(Gfull, paths, par, k, r=None, need_r=None):
    em = end_map(paths)
    P = [list(p) for p in paths]
    for v, p in par.items():
        i = em[v][0]
        Q = P[i]
        if Q[0] == v:
            Q.insert(0, p)
        elif Q[-1] == v:
            Q.append(p)
        else:  # v's end already moved (cannot happen: each vertex ends one path)
            return False
    used = set()
    for Q in P:
        if len(set(Q)) != len(Q) or len(Q) < 2:
            return False
        for x, y in zip(Q, Q[1:]):
            e = frozenset((x, y))
            if not Gfull.has_edge(x, y) or e in used:
                return False
            used.add(e)
    if len(used) != Gfull.number_of_edges() or len(P) > k:
        return False
    if r is not None:
        ends = sum((Q[0] == r) + (Q[-1] == r) for Q in P)
        if ends < need_r:
            return False
    return True


def rand_connected(n, p, rng):
    while True:
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(10**9))
        if nx.is_connected(G):
            return G


def claim1(rng, trials, nvals):
    agree = dis = total_dec = capped = 0
    exists = graphs = 0
    for t in range(trials):
        n = rng.choice(nvals)
        G = rand_connected(n, rng.uniform(0.3, 0.6), rng)
        T = [v for v in G if G.degree(v) % 2 == 0]
        J = min_tjoin(G, T)
        Jg = nx.Graph([tuple(e) for e in J])
        assert nx.is_forest(Jg) if J else True
        F = G.copy()
        F.remove_edges_from([tuple(e) for e in J])
        assert all(F.degree(v) % 2 == 1 for v in F), "F not all-odd"
        decs = lovasz_decomps(F)
        capped += len(decs) >= CAP
        k = n // 2
        roots = rootings(J, rng=rng)
        graphs += 1
        anyok = False
        for D in decs:
            total_dec += 1
            for par in roots:
                pr = predicate(D, par)
                ok = append_and_check(G, D, par, k)
                if pr == ok:
                    agree += 1
                else:
                    dis += 1
                    print("CLAIM1 DISAGREE", sorted(G.edges()), D, par, pr, ok, flush=True)
                anyok |= ok
        exists += anyok
    print(f"CLAIM1: graphs={graphs} decomps={total_dec} (capped graphs {capped}) "
          f"iff-agree={agree} disagree={dis}; graphs with some (D, rooting) valid={exists}/{graphs}",
          flush=True)


def gen_J(n, D, rng, three=True):
    while True:
        G = nx.gnp_random_graph(n, rng.uniform(0.35, 0.6), seed=rng.randrange(10**9))
        G.remove_edges_from(list(G.edges(0)))
        U = rng.sample(range(1, n), D)
        for u in U:
            G.add_edge(0, u)
        bad = [v for v in range(1, n) if G.degree(v) % 2 == 0]
        rng.shuffle(bad)
        okp = True
        for i in range(0, len(bad), 2):
            u, v = bad[i], bad[i + 1]
            if G.has_edge(u, v):
                G.remove_edge(u, v)
            else:
                G.add_edge(u, v)
        if G.degree(0) != D or any(G.degree(v) % 2 == 0 for v in range(1, n)):
            continue
        if min(d for _, d in G.degree()) < 3 or not nx.is_connected(G):
            continue
        if three and nx.node_connectivity(G) < 3:
            continue
        if not three and nx.node_connectivity(G) < 2:
            continue
        return G


def claim2(rng, trials, nvals, Dz):
    par_ok = par_bad = lifts = lift_fail = inst = inst_ok = longcomp = 0
    for t in range(trials):
        n = rng.choice(nvals)
        J = gen_J(n, Dz, rng)
        U = sorted(J.neighbors(0))
        for r in U:
            for w in [u for u in U if u != r][:2]:
                T = [u for u in U if u not in (r, w)]
                H = J.copy(); H.remove_nodes_from([0, r])
                if not nx.is_connected(H):
                    print("H disconnected?!"); continue
                JT = min_tjoin(H, T)
                Jg = nx.Graph([tuple(e) for e in JT])
                assert nx.is_forest(Jg)
                assert all(0 not in e and r not in e for e in JT)
                longcomp += any(len(c) > 2 for c in nx.connected_components(Jg))
                M = J.copy()
                M.remove_edges_from([(0, w)] + [(0, v) for v in T] + [tuple(e) for e in JT])
                # parity claims
                good = (M.degree(0) == 1 and M.has_edge(0, r) and M.degree(r) == J.degree(r)
                        and M.degree(r) % 2 == 1 and M.degree(r) >= 3 and M.degree(w) % 2 == 0
                        and all(M.degree(v) % 2 == 1 and M.degree(v) >= 1
                                for v in M if v not in (w,)))
                par_ok += good; par_bad += (not good)
                if not good:
                    print("PARITY FAIL", sorted(J.edges()), r, w, flush=True)
                Mw = M.copy()
                if Mw.degree(w) == 0:
                    Mw.remove_node(w)
                decs = lovasz_decomps(Mw, cap=1500)
                roots = rootings(JT, forced_root=w if w in Jg else None, rng=rng)
                inst += 1
                k = (n - 1) // 2
                found = False
                for D0 in decs:
                    # Step 1: delete z
                    paths = [list(p) for p in D0]
                    iz = [i for i, p in enumerate(paths) if p[0] == 0 or p[-1] == 0]
                    P = paths[iz[0]]
                    if P[-1] == 0:
                        P.reverse()
                    if len(P) >= 3:
                        paths[iz[0]] = P[1:]
                    else:
                        del paths[iz[0]]
                        for i, Q in enumerate(paths):
                            if r in Q[1:-1]:
                                j = Q.index(r)
                                paths[i:i + 1] = [Q[:j + 1], Q[j:]]
                                break
                    for parm in roots:
                        if not predicate(D0, parm):
                            continue
                        lifts += 1
                        B = J.copy(); B.remove_node(0)
                        ok = append_and_check(B, paths, parm, k, r=r, need_r=2)
                        if ok:
                            found = True
                        else:
                            lift_fail += 1
                            print("LIFT FAIL", sorted(J.edges()), r, w, D0, parm, flush=True)
                inst_ok += found
    print(f"CLAIM2 (d(z)={Dz}): parity ok {par_ok}, parity fail {par_bad}; instances {inst} "
          f"(with a J_T component of >= 3 vertices: {longcomp}); lifts attempted {lifts}, "
          f"lift failures {lift_fail}; instances with a valid (Q0, rooting) {inst_ok}/{inst}",
          flush=True)


def claim3(rng, trials, nvals):
    comp_viol = 0
    inst = both_inadm = both_inadm_big = or_fail = or_fail_big = 0
    examples = []
    for t in range(trials):
        n = rng.choice(nvals)
        J = gen_J(n, 4, rng, three=False)  # 2-connected
        U = sorted(J.neighbors(0))
        for r in U:
            for w in U:
                if w == r:
                    continue
                a, b = [u for u in U if u not in (r, w)]
                if not J.has_edge(a, b):
                    continue
                inst += 1
                M = J.copy()
                M.remove_edges_from([(0, w), (0, a), (0, b), (a, b)])
                odd = {v for v in M if M.degree(v) % 2 == 1}
                for C in nx.connected_components(M):
                    if (C & odd) == {a, b}:
                        comp_viol += 1
                        print("COMPONENT VIOLATION", sorted(J.edges()), r, w, a, b, flush=True)
                C = next(c for c in nx.connected_components(M) if a in c)
                ev = [v for v in M if M.degree(v) > 0 and M.degree(v) % 2 == 0]
                adm_ab = not M.has_edge(b, a) and all(not M.has_edge(g, a) for g in ev)  # c=b, A={a}
                adm_ba = not M.has_edge(a, b) and all(not M.has_edge(g, b) for g in ev)  # c=a, A={b}
                big = len(C & odd) >= 4 and b in C
                if not adm_ab and not adm_ba:
                    both_inadm += 1
                    both_inadm_big += big
                    if big and len(examples) < 2:
                        examples.append((sorted(J.edges()), r, w, a, b))
                decs = lovasz_decomps(M, cap=3000)
                ok = False
                for D in decs:
                    em = end_map(D)
                    if a not in D[em[b][0]] or b not in D[em[a][0]]:
                        ok = True
                        break
                if not ok:
                    or_fail += 1
                    or_fail_big += big
                    print("OR FAIL (within cap %d decomps)" % len(decs), sorted(J.edges()), r, w, a, b,
                          flush=True)
    print(f"CLAIM3: instances {inst}; component violations {comp_viol}; neither direction "
          f"L1*-admissible: {both_inadm} (of which |C cap Odd| >= 4: {both_inadm_big}); "
          f"OR failures {or_fail} (big {or_fail_big})", flush=True)
    for ex in examples:
        print("  inadmissible-both example:", ex, flush=True)


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    which = sys.argv[2] if len(sys.argv) > 2 else "123"
    if "1" in which:
        claim1(rng, 40, [6, 8])
    if "2" in which:
        claim2(rng, 12, [9, 11], 4)
        claim2(rng, 8, [9, 11], 6)
    if "3" in which:
        claim3(rng, 40, [7, 9])

"""A16: tests of the route-descent reductions of route-descent.tex (Sections 3-7).

  basics   Lemma 5 (basic facts), Lemma 7 (heredity of Thm-21 systems), Lemma 11 (1)-(5) and
           Corollary 12, on independently built Thm-21 systems (forest T-joins: spanning-tree and
           minimum; random edge-disjoint linkings in every F^v).
  bij      Lemma 9 and Proposition 15 as BIJECTIONS: on small graphs with random route systems
           (any edge-disjoint routes), count by exhaustive enumeration
             #{realisations of M in G with R_p terminal at a}  vs
             #{realisations of M - a in G' with V(Q_c) n V(R_p) = {c}},
           and #{route-respecting realisations of M} vs #{M-compatible Lovasz decompositions of F},
           and apply the maps of the proofs to every object.
  sched    Theorem 28 (route schedules) and Theorem 26 by running their proofs (Lovasz on F, then
           Lemma 3 edge by edge); checks of the remarks after Theorem 26 / Definition 27.
  upm      Corollary 29 by running its proof.
  packed   Corollary 23, and the remark after it (a route system with a cycle in J).
  unlinked Section 8 "Linking is needed": re-check an instance of the manuscript's unlinked.py.

Usage: python3 a16_route_test.py MODE [trials] [seed]
"""
import itertools
import random
import sys

import a16_core as C
import a16_sep_test as S

MMAX = 13

# ----------------------------------------------------------------------------------------------
# T-joins and Thm-21 systems


def bfs_path(adj, s, t, rng=None):
    par = {s: None}
    fr = [s]
    while fr and t not in par:
        nx_ = []
        for x in fr:
            N = sorted(adj[x], key=str)
            if rng:
                rng.shuffle(N)
            for y in N:
                if y not in par:
                    par[y] = x
                    nx_.append(y)
        fr = nx_
    if t not in par:
        return None
    P = [t]
    while par[P[-1]] is not None:
        P.append(par[P[-1]])
    return P[::-1]


def min_matching_cost(T, d):
    T = list(T)
    memo = {}

    def f(mask):
        if mask == 0:
            return 0, []
        if mask in memo:
            return memo[mask]
        i = (mask & -mask).bit_length() - 1
        best = (float("inf"), None)
        for j in range(i + 1, len(T)):
            if mask >> j & 1:
                c, m = f(mask & ~(1 << i) & ~(1 << j))
                c += d[T[i]].get(T[j], float("inf"))
                if c < best[0]:
                    best = (c, [(T[i], T[j])] + m)
        memo[mask] = best
        return best

    return f((1 << len(T)) - 1)


def min_tjoin(adj, T, rng):
    """A minimum T-join: symmetric difference of shortest paths along a min-cost matching of T
    (its size is at most the matching cost, which is a lower bound for every T-join)."""
    d = {s: C.dist_from(adj, s) for s in T}
    cost, M = min_matching_cost(T, d)
    assert cost < float("inf")
    J = set()
    for s, t in M:
        P = bfs_path(adj, s, t, rng)
        for e in zip(P, P[1:]):
            J ^= {frozenset(e)}
    assert len(J) <= cost
    return J, cost


def tjoin_odd(J, V):
    dg = {v: 0 for v in V}
    for e in J:
        for x in e:
            dg[x] += 1
    return {v for v in V if dg[v] % 2}


def is_forest(J, V):
    par = {v: v for v in V}

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for e in J:
        x, y = tuple(e)
        rx, ry = find(x), find(y)
        if rx == ry:
            return False
        par[rx] = ry
    return True


def tree_tjoin(adj, T, rng):
    V = list(adj)
    rng.shuffle(V)
    seen = set()
    tree = []
    for r in V:
        if r in seen:
            continue
        seen.add(r)
        st = [r]
        while st:
            x = st.pop(rng.randrange(len(st)))
            N = sorted(adj[x], key=str)
            rng.shuffle(N)
            for y in N:
                if y not in seen:
                    seen.add(y)
                    tree.append(frozenset((x, y)))
                    st.append(y)
    # the T-join inside the tree: edge e in J iff one side of e contains an odd number of T
    tadj = {v: set() for v in adj}
    for e in tree:
        x, y = tuple(e)
        tadj[x].add(y)
        tadj[y].add(x)
    J = set()
    seen = set()
    for r in adj:
        if r in seen:
            continue
        order, par = [], {r: None}
        st = [r]
        seen.add(r)
        while st:
            x = st.pop()
            order.append(x)
            for y in tadj[x]:
                if y not in par:
                    par[y] = x
                    seen.add(y)
                    st.append(y)
        cnt = {v: (1 if v in T else 0) for v in order}
        for x in reversed(order):
            if par[x] is not None:
                if cnt[x] % 2:
                    J.add(frozenset((x, par[x])))
                cnt[par[x]] += cnt[x]
    return J


def free_graph_at(adj, F, v):
    """F^v: F with the edges at v deleted and v joined to every vertex of V - v - N_G(v)."""
    H = C.copy(F)
    for w in list(H[v]):
        C.del_edge(H, v, w)
    for w in adj:
        if w != v and w not in adj[v]:
            C.add_edge(H, v, w)
    return H


def random_linking(H, rng):
    """Pair the odd vertices of H by edge-disjoint paths of H (greedy, random)."""
    H = C.copy(H)
    out = []
    while True:
        odd = sorted((x for x in H if len(H[x]) % 2), key=str)
        if not odd:
            return out
        x = rng.choice(odd)
        dd = C.dist_from(H, x)
        cand = [y for y in odd if y != x and y in dd]
        assert cand, "odd vertex alone in its component"
        y = rng.choice(cand)
        P = bfs_path(H, x, y, rng)
        for e in zip(P, P[1:]):
            C.del_edge(H, *e)
        out.append(P)


def thm21_system(adj, J, rng):
    """The construction of [EMM, Thm 21] on a forest T-join J: at each v pair the odd vertices of
    F^v by edge-disjoint paths; follow the transitions. Returns (routes, links)."""
    V = list(adj)
    Jadj = {v: set() for v in V}
    for e in J:
        x, y = tuple(e)
        Jadj[x].add(y)
        Jadj[y].add(x)
    F = {v: {w for w in adj[v] if frozenset((v, w)) not in J} for v in V}
    nxt, links = {}, {}
    for v in V:
        if not Jadj[v]:
            continue
        Fv = free_graph_at(adj, F, v)
        odd = {x for x in Fv if len(Fv[x]) % 2}
        expect = set(Jadj[v]) | ({v} if len(adj[v]) % 2 == 0 else set())
        assert odd == expect, "EMM Lemma 19 (free degrees) fails"
        L = random_linking(Fv, rng)
        links[v] = L
        for P in L:
            x, y = P[0], P[-1]
            if x == v:
                nxt[(v, y)] = None
            elif y == v:
                nxt[(v, x)] = None
            else:
                nxt[(v, x)] = y
                nxt[(v, y)] = x
    used, routes = set(), []
    for v in V:
        for w in Jadj[v]:
            if nxt.get((v, w), 0) is None and frozenset((v, w)) not in used:
                R = [v]
                prev, cur = v, w
                while True:
                    used.add(frozenset((prev, cur)))
                    R.append(cur)
                    nn = nxt[(cur, prev)]
                    if nn is None:
                        break
                    prev, cur = cur, nn
                routes.append(R)
    assert used == J, "transitions leave a closed trail"
    return routes, links, F


def route_edges(R):
    return {frozenset(e) for e in zip(R, R[1:])}


def transitions_at(routes, v):
    tr = set()
    for R in routes:
        if v in R:
            i = R.index(v)
            if 0 < i < len(R) - 1:
                tr.add(frozenset((R[i - 1], R[i + 1])))
            elif i == 0:
                tr.add(frozenset((R[1], v)))
            else:
                tr.add(frozenset((R[-2], v)))
    return tr


def check_thm21(adj, routes, links, F):
    """Definition 4: J a forest; at every v, edge-disjoint paths of F^v linking the transitions."""
    J = set().union(*[route_edges(R) for R in routes]) if routes else set()
    assert is_forest(J, adj)
    for v in adj:
        tr = transitions_at(routes, v)
        L = [P for P in links.get(v, []) if frozenset((P[0], P[-1])) in tr]
        assert {frozenset((P[0], P[-1])) for P in L} == tr, "a transition is not linked"
        Fv = free_graph_at(adj, F, v)
        usedE = set()
        for P in L:
            for e in zip(P, P[1:]):
                f = frozenset(e)
                assert e[1] in Fv[e[0]] and f not in usedE, "linking path not in F^v / not disjoint"
                usedE.add(f)


def random_instance(rng, nmin=6, nmax=12):
    for _ in range(100):
        n = rng.choice(range(nmin, nmax + 1, 2))
        adj = C.random_graph(n, rng.uniform(0.2, 0.6), rng)
        if any(not adj[v] for v in adj):
            continue
        # connected?
        if len(C.dist_from(adj, 0)) != n:
            continue
        if len(C.even_set(adj)) >= 2:
            return adj
    return None


# ----------------------------------------------------------------------------------------------
# basics: Lemmas 5, 7, 11, Corollary 12


def test_basics(trials, rng):
    cnt = dict(systems=0, routes=0, geodesic_checks=0)
    for _ in range(trials):
        adj = random_instance(rng)
        if adj is None:
            continue
        T = set(C.even_set(adj))
        for kind in ("tree", "min"):
            if kind == "min":
                J, cost = min_tjoin(adj, T, rng)
                assert len(J) == cost
            else:
                J = tree_tjoin(adj, T, rng)
            assert tjoin_odd(J, adj) == T
            if kind == "min":
                assert is_forest(J, adj), "Lemma 11(1): minimum T-join not a forest"
            else:
                assert is_forest(J, adj)
            routes, links, F = thm21_system(adj, J, rng)
            check_thm21(adj, routes, links, F)
            cnt["systems"] += 1
            # Lemma 5
            for v in adj:
                assert len(F[v]) % 2 == 1, "Lemma 5: even free degree"
            for R in routes:
                for x in R[1:-1]:
                    assert len(adj[x]) >= 3, "Lemma 5: interior vertex of degree < 3"
            if kind == "min":
                d = {s: C.dist_from(adj, s) for s in adj}
                for R in routes:
                    for i in range(len(R)):
                        for j in range(i + 1, len(R)):
                            assert d[R[i]][R[j]] == j - i, "Lemma 11(3): segment not a geodesic"
                            cnt["geodesic_checks"] += 1
                # Lemma 11(2) on random cycles: |C n J| <= |C - J|
                for _ in range(20):
                    e = rng.choice(sorted(C.edges(adj), key=lambda f: sorted(map(str, f))))
                    x, y = tuple(e)
                    H = C.copy(adj)
                    C.del_edge(H, x, y)
                    P = bfs_path(H, x, y, rng)
                    if P:
                        cyc = route_edges(P) | {e}
                        assert len(cyc & J) <= len(cyc - J), "Lemma 11(2)"
            # Lemma 7 for every route, Lemma 11(4), Corollary 12
            for R in routes:
                cnt["routes"] += 1
                a, c = R[0], R[-1]
                G2 = C.copy(adj)
                for e in zip(R, R[1:]):
                    C.del_edge(G2, *e)
                assert all(G2[v] for v in G2), "Lemma 7: isolated vertex"
                seen = set()
                for s in G2:
                    if s not in seen:
                        comp = C.dist_from(G2, s)
                        seen |= set(comp)
                        assert len(comp) % 2 == 0, "Lemma 7: odd component"
                assert set(C.even_set(G2)) == T - {a, c}, "Lemma 7: Ev(G')"
                rest = [Q for Q in routes if Q is not R]
                J2 = J - route_edges(R)
                F2 = {v: {w for w in G2[v] if frozenset((v, w)) not in J2} for v in G2}
                assert all(F2[v] == F[v] for v in adj), "Lemma 7: free graph changed"
                links2 = {}
                for v in adj:
                    tr = transitions_at(rest, v)
                    links2[v] = [P for P in links.get(v, []) if frozenset((P[0], P[-1])) in tr]
                check_thm21(G2, rest, links2, F2)
                if kind == "min":
                    _, cost2 = min_tjoin(G2, T - {a, c}, rng)
                    assert cost2 == len(J) - (len(R) - 1), "Lemma 11(4)"
                    for v in (a, c):
                        assert set(G2[v]) - set(R), "Corollary 12"
        # Lemma 11(5): a T-join that is a matching (a perfect matching of G[Ev]) is minimum
        pm = next(perfect_matchings(sorted(T, key=str), adj), None)
        if pm is not None:
            _, cost = min_tjoin(adj, T, rng)
            assert cost == len(pm), "Lemma 11(5)"
            cnt["matching_tjoins"] = cnt.get("matching_tjoins", 0) + 1
    print("basics:", cnt, "- Lemmas 5, 7, 11(1)-(4), Corollary 12: no violation")


# ----------------------------------------------------------------------------------------------
# bijections: Lemma 9 and Proposition 15


def random_route_system(adj, rng, tries=50):
    """A random route system (Definition 4, no linking condition): a pairing of Ev with
    edge-disjoint paths."""
    T = C.even_set(adj)
    for _ in range(tries):
        rng.shuffle(T)
        pairs = [(T[2 * i], T[2 * i + 1]) for i in range(len(T) // 2)]
        H = C.copy(adj)
        routes = []
        ok = True
        for s, t in pairs:
            # random path s-t in H (random DFS)
            P = None
            for _ in range(10):
                st = [[s]]
                while st:
                    Q = st.pop()
                    if Q[-1] == t:
                        P = Q
                        break
                    N = [w for w in H[Q[-1]] if w not in Q]
                    rng.shuffle(N)
                    for w in N:
                        st.append(Q + [w])
                    if len(st) > 2000:
                        break
                if P:
                    break
            if not P:
                ok = False
                break
            for e in zip(P, P[1:]):
                C.del_edge(H, *e)
            routes.append(P)
        if ok:
            return routes
    return None


def profile(adj, M):
    return {v: (len(adj[v]) % 2 if len(adj[v]) % 2 else (2 if v in M else 0)) if adj[v] else 0
            for v in adj}


def canon_partition(D):
    return frozenset(tuple(P) if (str(P[0]), str(P[-1])) <= (str(P[-1]), str(P[0])) else tuple(P[::-1])
                     for P in D)


def test_bij(trials, rng):
    tot9 = tot15 = nz9 = nz15 = obj9 = obj15 = 0
    for _ in range(trials):
        n = rng.choice([6, 8])
        adj = C.random_graph(n, rng.uniform(0.3, 0.55), rng)
        m = len(C.edges(adj))
        if any(not adj[v] for v in adj) or m > MMAX or len(C.even_set(adj)) < 2:
            continue
        if any(len(C.dist_from(adj, s)) % 2 for s in adj):
            continue
        routes = random_route_system(adj, rng)
        if routes is None:
            continue
        for R in routes:  # orient: R from head a (R[0]) to tail c (R[-1]) at random
            if rng.random() < 0.5:
                R.reverse()
        heads = [R[0] for R in routes]
        tails = [R[-1] for R in routes]
        M = set(heads)
        J = set().union(*[route_edges(R) for R in routes])
        F = {v: {w for w in adj[v] if frozenset((v, w)) not in J} for v in adj}
        b = profile(adj, M)
        reals = list(C.partitions_with_profile(adj, b))
        # Lemma 9 for each p
        for R in routes:
            a, c = R[0], R[-1]
            G2 = C.copy(adj)
            for e in zip(R, R[1:]):
                C.del_edge(G2, *e)
            b2 = profile(G2, M - {a})
            assert b2[a] == 1 and b2[c] == 1
            lhs = []  # (ii): R terminal at a
            for D in reals:
                ok = None
                for P in D:
                    for Q in (P, P[::-1]):
                        k = len(R)
                        if len(Q) >= k and Q[-k:] == R[::-1]:
                            ok = (D, P, Q)
                if ok:
                    lhs.append(ok)
            rhs = []
            for D2 in C.partitions_with_profile(G2, b2):
                (Qc,) = [P for P in D2 if c in (P[0], P[-1])]
                if set(Qc) & set(R) == {c}:
                    rhs.append((D2, Qc))
            # apply the maps
            imgs = set()
            for D2, Qc in rhs:
                Q = Qc if Qc[-1] == c else Qc[::-1]
                newP = Q + R[::-1][1:]
                D = [P for P in D2 if P is not Qc] + [newP]
                C.check_partition(adj, D, b)
                imgs.add(canon_partition(D))
            pre = set()
            for D, P, Q in lhs:
                k = len(R)
                rest = Q[:-k + 1]
                assert len(rest) >= 2 and rest[-1] == c
                D2 = [X for X in D if X is not P] + [rest]
                C.check_partition(G2, D2, b2)
                (Qc,) = [X for X in D2 if c in (X[0], X[-1])]
                assert set(Qc) & set(R) == {c}
                pre.add(canon_partition(D))
            assert imgs == pre and len(imgs) == len(rhs) == len(lhs), (len(lhs), len(rhs))
            tot9 += 1
            nz9 += bool(lhs)
            obj9 += len(lhs)
        # Proposition 15
        rr = []
        for D in reals:
            # route-respecting: every route terminal at its head
            okall = True
            for R in routes:
                k = len(R)
                if not any(len(Q) >= k and Q[-k:] == R[::-1] for P in D for Q in (P, P[::-1])):
                    okall = False
                    break
            if okall:
                rr.append(D)
        compat = []
        tail_route = {R[-1]: R for R in routes}
        for D in C.lovasz_decompositions(F):
            good = True
            for P in D:
                for s in (P[0], P[-1]):
                    if s in tail_route and set(P) & set(tail_route[s]) != {s}:
                        good = False
                if P[0] in tail_route and P[-1] in tail_route:
                    if set(tail_route[P[0]]) & set(tail_route[P[-1]]):
                        good = False
            if good:
                compat.append(D)
        imgs = set()
        for D in compat:
            out = []
            for P in D:
                Q = list(P)
                if Q[-1] in tail_route:
                    Q = Q + tail_route[Q[-1]][::-1][1:]
                if Q[0] in tail_route:
                    Q = tail_route[Q[0]][:-1] + Q
                out.append(Q)
            C.check_partition(adj, out, b)
            imgs.add(canon_partition(out))
        assert imgs == {canon_partition(D) for D in rr} and len(compat) == len(rr), \
            (len(compat), len(rr))
        tot15 += 1
        nz15 += bool(rr)
        obj15 += len(rr)
    print(f"bij: Lemma 9 bijection verified for {tot9} (G, P, M, p) ({nz9} with a nonempty side, "
          f"{obj9} realisations matched); Proposition 15 bijection verified for {tot15} (G, P, M) "
          f"({nz15} nonempty, {obj15} route-respecting realisations matched)")


# ----------------------------------------------------------------------------------------------
# schedules: Theorems 26, 28; Corollary 29


def lovasz(adj, rng):
    D = S.sep(adj, [], rng)
    C.check_partition(adj, D, C.lovasz_profile(adj))
    return D


def is_schedule(adj, F, routes, order):
    """order: list of (route oriented tail -> head). Definition 27."""
    G = C.copy(F)
    U = set()
    for R in order:
        c = R[0]
        for x in R[1:]:
            if G[x] & (U | {c}):
                return False
        for e in zip(R, R[1:]):
            C.add_edge(G, *e)
        U.add(c)
    return True


def run_schedule(adj, F, order, rng):
    """Proof of Theorem 28."""
    D = lovasz(F, rng)
    G = C.copy(F)
    for R in order:
        for i in range(1, len(R)):
            t, u = R[i - 1], R[i]
            Gc, D, _ = C.fan(G, D, t, u)
            G = Gc
    heads = {R[-1] for R in order}
    b = profile(adj, heads)
    C.check_partition(adj, D, b)
    return D


def test_sched(trials, rng):
    nsched = nall = niso = 0
    for _ in range(trials):
        adj = random_instance(rng, 6, 14)
        if adj is None:
            continue
        T = set(C.even_set(adj))
        J, _ = min_tjoin(adj, T, rng) if rng.random() < 0.5 else (tree_tjoin(adj, T, rng), 0)
        routes, links, F = thm21_system(adj, J, rng)
        # Fan-isolated hypothesis (Theorem 26)
        iso = all((adj[x] & T) <= {R[i - 1] for i in [R.index(x)] if i > 0} |
                  {R[i + 1] for i in [R.index(x)] if i < len(R) - 1}
                  for R in routes for x in R)
        for _ in range(30):
            order = [R if rng.random() < 0.5 else R[::-1] for R in routes]
            rng.shuffle(order)
            if is_schedule(adj, F, routes, order):
                run_schedule(adj, F, order, rng)
                nsched += 1
                break
        if iso:
            niso += 1
            # every order and orientation is a schedule; G[Ev] is a matching
            for perm in itertools.islice(itertools.permutations(routes), 24):
                for flips in itertools.product([0, 1], repeat=len(routes)):
                    order = [R[::-1] if f else R for R, f in zip(perm, flips)]
                    assert is_schedule(adj, F, routes, order), "Thm 26 hypothesis but not a schedule"
            for v in T:
                assert len(adj[v] & T) <= 1, "Fan-isolated but G[Ev] not a matching"
                for w in adj[v] & T:
                    assert [v, w] in routes or [w, v] in routes
            nall += 1
    print(f"sched: Theorem 28 proof executed on {nsched} schedules (all outputs checked); "
          f"{niso} Fan-isolated systems: every order/orientation a schedule and G[Ev] a matching")


def perfect_matchings(V, adj):
    V = list(V)
    if not V:
        yield []
        return
    a = V[0]
    for b in V[1:]:
        if b in adj[a]:
            rest = [x for x in V if x not in (a, b)]
            for m in perfect_matchings(rest, adj):
                yield [(a, b)] + m


def test_upm(trials, rng):
    done = 0
    for _ in range(trials):
        n = rng.randint(6, 13)
        adj = C.random_graph(n, rng.uniform(0.2, 0.5), rng)
        if any(not adj[v] for v in adj):
            continue
        T = C.even_set(adj)
        if not T:
            continue
        pms = list(itertools.islice(perfect_matchings(sorted(T), adj), 2))
        if len(pms) != 1:
            continue
        N = pms[0]
        for _o in range(4):
            orient = [(c, a) if rng.random() < 0.5 else (a, c) for c, a in N]  # (tail, head)
            # proof of Corollary 29: repeatedly remove a sink, then put back in reverse order
            G = C.copy(adj)
            rem = list(orient)
            stack = []
            while rem:
                sinks = [i for i, (c, a) in enumerate(rem)
                         if not any(rem[j][0] in adj[a] for j in range(len(rem)) if j != i)]
                assert sinks, "relation not acyclic although N is unique"
                i = rng.choice(sinks)
                stack.append(rem.pop(i))
            for c, a in stack:
                C.del_edge(G, c, a)
            assert not C.even_set(G) or all(len(G[v]) % 2 for v in G if G[v])
            D = lovasz(G, rng)
            for c, a in reversed(stack):
                G, D, _ = C.fan(G, D, c, a)
            C.check_partition(adj, D, profile(adj, {a for c, a in orient}))
            done += 1
    print(f"upm: Corollary 29 proof executed on {done} orientations (all outputs checked)")


# ----------------------------------------------------------------------------------------------
# Corollary 23 and the remark after it


def test_packed(trials, rng):
    # the remark: J may contain a cycle for a general route system with V(J) packed in F
    E = []
    J = [("v1", "v2"), ("v3", "v4"), ("x", "v2"), ("v2", "v3"), ("v3", "y"),
         ("xx", "v4"), ("v4", "v1"), ("v1", "yy")]
    routes = [["v1", "v2"], ["v3", "v4"], ["x", "v2", "v3", "y"], ["xx", "v4", "v1", "yy"]]
    E += J
    Vj = sorted({x for e in J for x in e})
    for v in Vj:
        E.append((v, "leaf_" + v))
    adj = {}
    for u, v in E:
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)
    Jset = {frozenset(e) for e in J}
    F = {v: {w for w in adj[v] if frozenset((v, w)) not in Jset} for v in adj}
    assert set(C.even_set(adj)) == set(Vj)
    assert C.packed(F, Vj)
    assert not is_forest(Jset, adj)
    rng2 = random.Random(5)
    D = S.sep(F, Vj, rng2)
    cnt = 0
    for flips in itertools.product([0, 1], repeat=len(routes)):
        orient = [R[::-1] if f else R for R, f in zip(routes, flips)]  # tail first
        tail_route = {R[0]: R for R in orient}
        out = []
        for P in D:
            Q = list(P)
            if Q[-1] in tail_route:
                Q = Q + tail_route[Q[-1]][1:]
            if Q[0] in tail_route:
                Q = tail_route[Q[0]][::-1][:-1] + Q
            out.append(Q)
        C.check_partition(adj, out, profile(adj, {R[-1] for R in orient}))
        cnt += 1
    print(f"packed: route system with a 4-cycle v1v2v3v4 in J and V(J) packed in F (n = {len(adj)}):"
          f" G[Ev] = J is not a forest; one decomposition of F realises all {cnt} transversals")
    # random instances of Corollary 23
    done = 0
    for _ in range(trials):
        adj = random_instance(rng, 6, 14)
        if adj is None:
            continue
        T = set(C.even_set(adj))
        J, _ = min_tjoin(adj, T, rng)
        routes, links, F = thm21_system(adj, J, rng)
        Vj = sorted({x for e in J for x in e}, key=str)
        if not C.packed(F, Vj):
            continue
        D = S.sep(F, Vj, rng)
        for flips in itertools.product([0, 1], repeat=len(routes)):
            orient = [R[::-1] if f else R for R, f in zip(routes, flips)]
            tail_route = {R[0]: R for R in orient}
            out = []
            for P in D:
                Q = list(P)
                if Q[-1] in tail_route:
                    Q = Q + tail_route[Q[-1]][1:]
                if Q[0] in tail_route:
                    Q = tail_route[Q[0]][::-1][:-1] + Q
                out.append(Q)
            C.check_partition(adj, out, profile(adj, {R[-1] for R in orient}))
        done += 1
    print(f"packed: Corollary 23 verified on {done} random minimum Thm-21 systems with V(J) packed")


# ----------------------------------------------------------------------------------------------
# Section 8, "Linking is needed": an instance found by the manuscript's unlinked.py, re-checked here


def all_linkings(H, pairs_needed):
    """Is there a family of pairwise edge-disjoint paths of H joining each pair in pairs_needed?"""
    if not pairs_needed:
        return True
    (x, y), rest = pairs_needed[0], pairs_needed[1:]
    # all simple x-y paths in H
    st = [[x]]
    while st:
        P = st.pop()
        if P[-1] == y:
            H2 = C.copy(H)
            for e in zip(P, P[1:]):
                C.del_edge(H2, *e)
            if all_linkings(H2, rest):
                return True
            continue
        for w in H[P[-1]]:
            if w not in P:
                st.append(P + [w])
    return False


def test_unlinked(trials, rng):
    E = [(0, 4), (0, 8), (1, 2), (1, 8), (1, 9), (2, 3), (2, 6), (2, 9), (4, 7), (4, 8), (5, 9),
         (6, 9), (7, 8)]
    routes = [[0, 8], [2, 6], [7, 8, 1, 9]]
    adj = {v: set() for v in range(10)}
    for u, v in E:
        C.add_edge(adj, u, v)
    T = set(C.even_set(adj))
    J = set().union(*[route_edges(R) for R in routes])
    assert tjoin_odd(J, adj) == T and {R[0] for R in routes} | {R[-1] for R in routes} == T
    _, cost = min_tjoin(adj, T, rng)
    print(f"unlinked: Ev = {sorted(T)}, |J| = {len(J)}, minimum T-join size = {cost}")
    F = {v: {w for w in adj[v] if frozenset((v, w)) not in J} for v in adj}
    bad = []
    for v in adj:
        tr = transitions_at(routes, v)
        if tr and not all_linkings(free_graph_at(adj, F, v), [tuple(t) for t in tr]):
            bad.append(v)
    print("  vertices whose transitions cannot be linked in F^v:", bad)
    for M in ([8, 2, 9], [8, 6, 9]):
        b = profile(adj, set(M))
        n = sum(1 for _ in C.partitions_with_profile(adj, b))
        print(f"  transversal {M}: {n} realisations (exhaustive enumeration)")
        assert n == 0
    # the same pairing with linked routes?
    pairs = [(R[0], R[-1]) for R in routes]
    print("  pairing", pairs)


def main():
    mode = sys.argv[1]
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    rng = random.Random(seed)
    {"basics": test_basics, "bij": test_bij, "sched": test_sched, "upm": test_upm,
     "packed": test_packed, "unlinked": test_unlinked}[mode](trials, rng)


if __name__ == "__main__":
    main()

"""fb_nodata.py: the forest base (direct-test1 Conjecture 4.5) at roots without triangle data
(session claude/triangle-base, at the coordinator's request).

For every 3-connected J (graph6, z = the unique even vertex, d(z) >= 4) and every root r in N(z)
with no triangle data (J[N(z) - r] has no matching of size m - 1):
  * Test1 at r is decided exactly (tb.test1_exact, profiles with b <= 3);
  * the forest base is searched: for w in N(z) - r, T = N(z) - {r, w}, forest T-joins Phi of
    H = J - {z, r} (the T-join inside a spanning tree S of H is a forest, and every forest T-join
    arises this way; S ranges over BFS trees and random spanning trees, at most --phis distinct Phi
    per w), and rootings (w's component rooted at w; other components at most --roots rootings).
    Conditions (i) p(v) not in Q0(v) and (ii) siblings on different paths are exactly the
    route-respecting query C of route_ext.c with r_v = {v, p(v)} for non-root v and r_v = {v}
    otherwise: a path ending at v meets r_v only in v, and a path with ends x, y needs
    r_x, r_y disjoint, which for siblings fails at the common parent.
  * every base found is lifted (Theorem 4.2) and the result is verified as a Test1 decomposition.

usage: fb_nodata.py ORACLE FILE.g6 [--budget B] [--phis K] [--roots R] [--stride S]
"""
import argparse
import itertools
import random
from collections import Counter

import networkx as nx

from tb import data_choices, even_vertex, run_oracle, test1_exact, verify_test1, parse_paths


def tjoin_in_tree(S, T):
    """The unique T-join of the tree (or forest) S: edges whose removal splits T oddly."""
    Tset = set(T)
    out = []
    for comp in nx.connected_components(S):
        St = S.subgraph(comp)
        root = next(iter(comp))
        parent = {root: None}
        order = [root]
        for u in order:
            for v in St[u]:
                if v not in parent:
                    parent[v] = u
                    order.append(v)
        cnt = {u: int(u in Tset) for u in comp}
        for u in reversed(order):
            if parent[u] is not None:
                if cnt[u] % 2 == 1:
                    out.append((parent[u], u))
                cnt[parent[u]] += cnt[u]
    return frozenset(frozenset(e) for e in out)


def spanning_trees(H, rng, k):
    seen = []
    for s in sorted(H):
        seen.append(nx.bfs_tree(H, s).to_undirected())
    for _ in range(k):
        Hw = H.copy()
        for a, b in Hw.edges():
            Hw[a][b]["weight"] = rng.random()
        seen.append(nx.minimum_spanning_tree(Hw))
    return seen


def rootings(Phi_edges, w, cap, rng):
    F = nx.Graph()
    F.add_edges_from(tuple(e) for e in Phi_edges)
    comps = [sorted(c) for c in nx.connected_components(F)]
    choices = [[w] if w in c else c for c in comps]
    allr = list(itertools.product(*choices))
    rng.shuffle(allr)
    for roots in allr[:cap]:
        par = {}
        for c, rt in zip(comps, roots):
            for u, v in nx.bfs_edges(F.subgraph(c), rt):
                par[v] = u
        yield par


def forest_lift(J, z, r, par, D0):
    paths = [list(p) for p in D0]
    iz = [i for i, p in enumerate(paths) if p[0] == z or p[-1] == z]
    assert len(iz) == 1
    P = paths[iz[0]]
    if P[-1] == z:
        P.reverse()
    assert P[1] == r
    if len(P) >= 3:
        paths[iz[0]] = P[1:]
    else:
        del paths[iz[0]]
        for i, Q in enumerate(paths):
            if r in Q[1:-1]:
                j = Q.index(r)
                paths[i:i + 1] = [Q[:j + 1], Q[j:]]
                break
    # Lemma 4.1: append p(v) at the v-end of the path P(v) of D1 (ends taken in D1)
    endpath = {}
    for i, Q in enumerate(paths):
        endpath.setdefault(Q[0], []).append((i, 0))
        endpath.setdefault(Q[-1], []).append((i, 1))
    front, back = {}, {}
    for v, p in par.items():
        (i, side), = endpath[v]
        (front if side == 0 else back)[i] = p
    out = []
    for i, Q in enumerate(paths):
        Q = list(Q)
        if i in front:
            Q.insert(0, front[i])
        if i in back:
            Q.append(back[i])
        out.append(Q)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("oracle")
    ap.add_argument("file")
    ap.add_argument("--budget", type=int, default=2000000)
    ap.add_argument("--phis", type=int, default=30)
    ap.add_argument("--roots", type=int, default=8)
    ap.add_argument("--stride", type=int, default=1)
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    C = Counter()
    for ln, line in enumerate(open(args.file)):
        if ln % args.stride:
            continue
        J = nx.from_graph6_bytes(line.strip().encode())
        z = even_vertex(J)
        if z is None or J.degree(z) < 4 or nx.node_connectivity(J) < 3:
            continue
        n = J.number_of_nodes()
        for r in sorted(J[z]):
            if any(True for _ in data_choices(J, z, r)):
                continue
            C["roots_nodata"] += 1
            t1 = test1_exact(args.oracle, J, z, r)
            C["test1_%d" % t1] += 1
            H = J.copy()
            H.remove_nodes_from([z, r])
            found = False
            undec = False
            for w in sorted(J[z]):
                if w == r or found:
                    continue
                T = [u for u in J[z] if u not in (r, w)]
                phis = []
                for S in spanning_trees(H, rng, 3 * args.phis):
                    Ph = tjoin_in_tree(S, T)
                    if Ph not in phis:
                        phis.append(Ph)
                    if len(phis) >= args.phis:
                        break
                for Ph in phis:
                    if found:
                        break
                    M = J.copy()
                    M.remove_edges_from([(z, w)] + [(z, v) for v in T] + [tuple(e) for e in Ph])
                    E = list(M.edges())
                    b = [M.degree(v) % 2 for v in range(n)]
                    pars = list(rootings(Ph, w, args.roots, rng))
                    qs = []
                    for par in pars:
                        rv = [1 << v for v in range(n)]
                        for v, p in par.items():
                            rv[v] |= 1 << p
                        qs.append("WCB %d %d %s %s %s 7 %d" % (
                            n, len(E), " ".join("%d %d" % e for e in E), " ".join(map(str, b)),
                            " ".join(map(str, rv)), args.budget))
                    out = run_oracle(args.oracle, qs)
                    for par, o in zip(pars, out):
                        if o.startswith("1"):
                            D0 = parse_paths(o)
                            res = forest_lift(J, z, r, par, D0)
                            ok = verify_test1(J, z, r, res)
                            C["lift_ok" if ok else "LIFT_FAIL"] += 1
                            found = True
                            break
                        if o.startswith("2"):
                            undec = True
            if found:
                C["fb_found"] += 1
            else:
                C["fb_undec" if undec else "fb_none_within_cap"] += 1
                print("NOFB", nx.to_graph6_bytes(J, header=False).decode().strip(), "r=%d" % r,
                      "test1=%d" % t1, "undec=%d" % int(undec), flush=True)
            if t1 == 1 and not found:
                C["TEST1_BUT_NO_FB"] += 1
        if ln % 500 == 0:
            print("PROGRESS", ln, dict(C), flush=True)
    print("SUMMARY", dict(sorted(C.items())), flush=True)


if __name__ == "__main__":
    main()

"""verify_nd.py: independent check of the ND lines written by nd.c (nodata session).

For every line it rebuilds J from graph6 with networkx and checks, without using nd.c:
  * the instance: (T1) z is the only even vertex; (T2) z, r are the only even vertices, adjacent;
    J is 3-connected with minimum degree >= 3; J[N(z)] has no perfect matching (unless --all);
  * the data fields: nu(J[N(z)]), the Gallai-Edmonds sets (sizes, number of odd components, the
    class of r), the twin flags, the (T1) triangle-data flag;
  * when a base is reported: Phi = {v p(v)} is a forest of J - z whose odd vertices are exactly
    N(z); r is a root, or a child with c(r) >= 2; the tier claim (1: linear forest, components of
    length <= 2, every vertex <= 1 child; 2: linear forest, <= 1 child; 3: r a root; 4: r a child);
    D0 is a Lovasz decomposition of H = (J - z) - Phi (T1) or M = H + zr (T2); (i) and (ii);
  * the lift: the parent edges are appended at the child ends (parents first) and the result is
    verified as a (T1) decomposition (<= (n-1)/2 paths of J - z, >= 2 ends at r), or, for (T2),
    z is deleted as in test2 Thm 4.3 and the result verified (<= n/2 paths, >= 3 ends at r).
usage: python3 verify_nd.py [--all] [--t2] < ND lines
"""
import sys
from collections import Counter

import networkx as nx


def ge_decomp(G):
    nu = len(nx.max_weight_matching(G, maxcardinality=True))
    D = set()
    for v in G:
        H = G.copy()
        H.remove_node(v)
        if len(nx.max_weight_matching(H, maxcardinality=True)) == nu:
            D.add(v)
    A = set()
    for v in D:
        A |= set(G[v]) - D
    C = set(G) - D - A
    ncomp = nx.number_connected_components(G.subgraph(D)) if D else 0
    return nu, D, A, C, ncomp


def has_pm(G, S):
    H = G.subgraph(S)
    return 2 * len(nx.max_weight_matching(H, maxcardinality=True)) == len(S)


def paths_ok(K, paths):
    used = set()
    ends = Counter()
    for P in paths:
        assert len(P) >= 2 and len(set(P)) == len(P), P
        for a, b in zip(P, P[1:]):
            assert K.has_edge(a, b), (a, b)
            e = frozenset((a, b))
            assert e not in used, e
            used.add(e)
        ends[P[0]] += 1
        ends[P[-1]] += 1
    assert len(used) == K.number_of_edges()
    return ends


def main():
    allflag = "--all" in sys.argv
    st = Counter()
    for line in sys.stdin:
        if not line.startswith("ND "):
            continue
        g6 = line.split()[1]          # graph6 may contain '|'
        rest = line[3 + len(g6):]
        parts = rest.split("|")
        f = ["ND", g6] + parts[0].split()
        z, r = int(f[2]), int(f[3])
        dz, nu_, df, nD, nA, nC, ncomp = map(int, f[4:11])
        rc, twR, twO, tri, level = f[11], int(f[12]), int(f[13]), int(f[14]), int(f[15])
        J = nx.from_graph6_bytes(g6.encode())
        n = J.number_of_nodes()
        ev = sorted(v for v in J if J.degree(v) % 2 == 0)
        t2 = len(ev) == 2
        if t2:
            assert set(ev) == {z, r} and J.has_edge(z, r)
        else:
            assert ev == [z] and J.has_edge(z, r)
        assert min(d for _, d in J.degree()) >= 3 and nx.node_connectivity(J) >= 3
        T = set(J[z])
        G = J.subgraph(T)
        if not allflag:
            assert not has_pm(J, T)
        nu, D, A, C, nc = ge_decomp(nx.Graph(G))
        assert (dz, nu_, df, nD, nA, nC, ncomp) == (len(T), nu, len(T) - 2 * nu, len(D), len(A), len(C), nc)
        assert rc == ("D" if r in D else "A" if r in A else "C")
        tw = [(a, b) for a in T for b in T if a < b and J.degree(a) == 3 and set(J[a]) == set(J[b])]
        assert twR == int(any(r in p for p in tw)) and twO == int(any(r not in p for p in tw))
        if not t2:
            trich = any(has_pm(J, T - {r, w}) for w in T - {r})
            assert tri == int(trich)
        st[f"level {level}"] += 1
        if len(parts) < 3:
            continue
        pf = parts[1].split()
        assert pf[0] == "par"
        par = {v: int(p) for v, p in enumerate(pf[1:]) if int(p) >= 0}
        D0 = [list(map(int, p.split())) for p in parts[2:] if p.strip()]
        B = J.copy()
        B.remove_node(z)
        Phi = nx.Graph([(v, p) for v, p in par.items()])
        for v, p in par.items():
            assert B.has_edge(v, p)
        assert nx.is_forest(Phi)
        odd = {v for v in Phi if Phi.degree(v) % 2 == 1}
        assert odd == T, (odd, T)
        children = Counter(par.values())
        # each component has exactly one root (a vertex without parent)
        for comp in nx.connected_components(Phi):
            roots = [v for v in comp if v not in par]
            assert len(roots) == 1
        if r in par:
            assert children[r] >= 2
        maxch = max(children.values()) if children else 0
        linear = all(d <= 2 for _, d in Phi.degree())
        shortc = all(len(c) <= 3 for c in nx.connected_components(Phi))
        if level == 1:
            assert linear and shortc and maxch <= 1 and r not in par
        elif level == 2:
            assert linear and maxch <= 1 and r not in par
        elif level == 3:
            assert r not in par
        elif level == 4:
            assert r in par
        H = B.copy()
        H.remove_edges_from(Phi.edges())
        K = H.copy()
        if t2:
            K.add_edge(z, r)
        ends = paths_ok(K, D0)
        for v in K:
            assert ends[v] == K.degree(v) % 2 == 1, v
        Q = {}
        for P in D0:
            Q[P[0]] = P
            Q[P[-1]] = P
        for v, p in par.items():
            assert p not in Q[v], ("(i)", v, p)
        for x in par:
            for y in par:
                if x < y and par[x] == par[y]:
                    assert Q[x] is not Q[y], ("(ii)", x, y)
        # lift: parents first (BFS order from the roots)
        order = []
        for comp in nx.connected_components(Phi):
            root = [v for v in comp if v not in par][0]
            order += [v for v in nx.bfs_tree(Phi, root) if v != root]
        paths = [list(P) for P in D0]
        for v in order:
            p = par[v]
            # parents first: v's only end is still its own end in D0
            cand = [i for i in range(len(paths)) if paths[i][0] == v or paths[i][-1] == v]
            assert len(cand) == 1
            P = paths[cand[0]]
            if P[0] == v:
                P.insert(0, p)
            else:
                P.append(p)
            assert len(set(P)) == len(P), "lift made a non-path"
        if not t2:
            e = paths_ok(B, paths)
            assert len(paths) <= (n - 1) // 2 and e[r] >= 2
            st["T1 lift verified"] += 1
        else:
            # z is a leaf at r in M; delete it
            zp = [P for P in paths if z in P]
            assert len(zp) == 1
            P = zp[0]
            rest = [Q_ for Q_ in paths if Q_ is not P]
            if len(P) == 2:
                newp = rest
                e = paths_ok(B, newp) if newp else Counter()
                # split one path through r at r (Lemma floor); r has an end or is interior
                ok = False
                for i, Q_ in enumerate(newp):
                    if r in Q_[1:-1]:
                        k = Q_.index(r)
                        cand = newp[:i] + newp[i + 1:] + [Q_[:k + 1], Q_[k:]]
                        e2 = paths_ok(B, cand)
                        if len(cand) <= n // 2 and e2[r] >= 3:
                            ok = True
                            break
                if not ok:
                    assert len(newp) <= n // 2 and e[r] >= 3, "T2 drop case"
            else:
                P2 = P[1:] if P[0] == z else P[:-1]
                newp = rest + [P2]
                e = paths_ok(B, newp)
                assert len(newp) <= n // 2 and e[r] >= 3
            st["T2 lift verified"] += 1
    print("VERIFIED", dict(st))


if __name__ == "__main__":
    main()

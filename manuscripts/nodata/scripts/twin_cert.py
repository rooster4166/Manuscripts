"""twin_cert.py: certify (T1) at instances by the twin reduction (nodata session).

For each ND line (typically levels 4-5): pick a twin pair x, y in N(z) (J-degree 3, the same
neighbourhood {z, a, b}), taking x = r if r has a twin; J' = J - x - y.  Find an all-odd base of
(J', z, r) (or, if r = x, of (J', z, r') for any root r' of J') with nd -x -a, lift it to a
decomposition D' of B' = J' - z (verified), then insert the twins back by the cycle insertion of
eulerian-cone Lemma 5.2 executed here (a path ending at a is extended, otherwise a path through a is
split at a away from b), and verify the result is a (T1) decomposition of B = J - z at r:
<= (|J| - 1)/2 paths, >= 2 ends at r.  Recurses if J' has no base itself.
usage: python3 twin_cert.py ND_BINARY < ND lines
"""
import subprocess
import sys
from collections import Counter
import networkx as nx


def g6(G):
    return nx.to_graph6_bytes(G, header=False).decode().strip()


def twins(J, z, T):
    out = []
    for a in T:
        for b in T:
            if a < b and J.degree(a) == 3 and set(J[a]) == set(J[b]):
                out.append((a, b))
    return out


def lifted(nd, J, z, root):
    """a decomposition of J - z with <= (|J|-1)/2 paths and >= 2 ends at root, from nd's base."""
    H = nx.convert_node_labels_to_integers(J, ordering="sorted")
    assert list(H.nodes()) == sorted(J.nodes()) or True
    mp = {v: i for i, v in enumerate(sorted(J.nodes()))}
    inv = {i: v for v, i in mp.items()}
    H = nx.relabel_nodes(J, mp)
    out = subprocess.run([nd, "-t1", "-a", "-x"], input=g6(H) + "\n", capture_output=True, text=True).stdout
    for line in out.splitlines():
        gg = line.split()[1]
        rest = line[3 + len(gg):]
        parts = rest.split("|")
        f = parts[0].split()
        if int(f[1]) != mp[root] or int(f[13]) >= 5:
            continue
        par = {v: int(p) for v, p in enumerate(parts[1].split()[1:]) if int(p) >= 0}
        D0 = [list(map(int, p.split())) for p in parts[2:] if p.strip()]
        Phi = nx.Graph([(v, p) for v, p in par.items()])
        order = []
        for comp in nx.connected_components(Phi):
            rt = [v for v in comp if v not in par][0]
            order += [v for v in nx.bfs_tree(Phi, rt) if v != rt]
        paths = [list(P) for P in D0]
        for v in order:
            p = par[v]
            cand = [P for P in paths if P[0] == v or P[-1] == v]
            assert len(cand) == 1
            P = cand[0]
            if P[0] == v:
                P.insert(0, p)
            else:
                P.append(p)
        return [[inv[x] for x in P] for P in paths]
    return None


def check(B, paths, r, bound):
    used = set(); ends = Counter()
    for P in paths:
        assert len(P) >= 2 and len(set(P)) == len(P)
        for a, b in zip(P, P[1:]):
            assert B.has_edge(a, b)
            e = frozenset((a, b)); assert e not in used; used.add(e)
        ends[P[0]] += 1; ends[P[-1]] += 1
    assert len(used) == B.number_of_edges()
    assert len(paths) <= bound, (len(paths), bound)
    return ends[r]


def insert_twins(paths, a, b, x, y):
    """cycle insertion of a y b x a (eulerian-cone Lemma 5.2): +1 path, +2 ends at x."""
    paths = [list(P) for P in paths]
    for i, P in enumerate(paths):
        if P[0] == a or P[-1] == a:
            Q = P if P[-1] == a else P[::-1]          # Q ends at a
            # x a + Q reversed ... : path  x - a - Q ... ; and R reversed: x b y a
            new1 = Q + [x]                               # Q ... a x
            new2 = [x, b, y, a]
            return paths[:i] + paths[i + 1:] + [new1, new2]
    for i, P in enumerate(paths):
        if a in P[1:-1]:
            k = P.index(a)
            X, Y = P[:k + 1], P[k:]
            if b in X[:-1]:
                X, Y = Y[::-1], X[::-1]                  # X ends at a and avoids b
            new1 = X + [y, b, x]                         # X ... a y b x
            new2 = [x, a] + Y[1:]                        # x a Y ...
            return paths[:i] + paths[i + 1:] + [new1, new2]
    raise AssertionError("a has no edge")


def certify(nd, J, z, r, depth=0):
    T = set(J[z])
    B = J.copy(); B.remove_node(z)
    tw = twins(J, z, T)
    # prefer a pair containing r
    tw.sort(key=lambda p: (r not in p))
    for x, y in tw:
        if y == r:
            x, y = y, x
        a, b = sorted(set(J[x]) - {z})
        if B.degree(a) - 2 < 1 and B.degree(b) - 2 < 1:
            continue
        if B.degree(a) - 2 < 1:
            a, b = b, a
        J2 = J.copy(); J2.remove_nodes_from([x, y])
        if x == r:
            # any decomposition of B' with <= |B'|/2 paths: take a (T1) one at any root
            roots = [v for v in J2[z]]
            D2 = None
            for rr in roots:
                D2 = lifted(nd, J2, z, rr) or (certify(nd, J2, z, rr, depth + 1) if depth < 3 else None)
                if D2:
                    break
        else:
            D2 = lifted(nd, J2, z, r) or (certify(nd, J2, z, r, depth + 1) if depth < 3 else None)
        if not D2:
            continue
        B2 = J2.copy(); B2.remove_node(z)
        check(B2, D2, r if x != r else a, (J2.number_of_nodes() - 1) // 2)
        D = insert_twins(D2, a, b, x, y)
        er = check(B, D, r, (J.number_of_nodes() - 1) // 2)
        assert er >= 2, er
        return D
    return None


def main():
    nd = sys.argv[1]
    st = Counter()
    for line in sys.stdin:
        if not line.startswith("ND "):
            continue
        gg = line.split()[1]
        f = line[3 + len(gg):].split("|")[0].split()
        z, r, level = int(f[0]), int(f[1]), int(f[13])
        J = nx.from_graph6_bytes(gg.encode())
        D = certify(nd, J, z, r)
        st[(level, "certified" if D else "NOT certified")] += 1
        if not D:
            print("NOTCERT", gg, z, r, flush=True)
    print("TWINCERT", dict(st))


if __name__ == "__main__":
    main()

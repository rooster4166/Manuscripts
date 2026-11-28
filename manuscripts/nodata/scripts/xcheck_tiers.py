"""xcheck_tiers.py: independent check of the negative tier claims of nd.c (nodata session).

For every ND line with level L >= 2 it re-derives, without nd.c's enumerators or solver, that no
all-odd base exists in the tiers below L that this script covers:
  tier 1 (L >= 2): no linkage with paths of length <= 2, rooted at ends (r a root), has a base;
  tier 2 (L >= 3): no linkage at all (vertex-disjoint T-paths, interiors outside T), rooted at ends.
Linkages are built from networkx.all_simple_paths in B[(V - T) + {a, b}] and combined into
vertex-disjoint systems; every end-rooting is decided by tools/route_ext.c (query C, masks
{v, p(v)}), a separate exact solver.  Also checks, for L = 5, that the instance is one of the
fat-theta instances (J = K_{3,t} + h2h3 with z a hub of degree t, r a leaf), and reports others.
usage: python3 xcheck_tiers.py ROUTE_EXT < ND lines
"""
import itertools
import subprocess
import sys
from collections import Counter

import networkx as nx


class Oracle:
    def __init__(self, path):
        self.p = subprocess.Popen(["stdbuf", "-oL", path], stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, text=True, bufsize=1)

    def query(self, line):
        self.p.stdin.write(line + "\n")
        self.p.stdin.flush()
        return self.p.stdout.readline().strip()


def linkages(B, T, maxlen):
    T = sorted(T)
    nonT = set(B) - set(T)
    paths = {}
    for a, b in itertools.combinations(T, 2):
        S = B.subgraph(nonT | {a, b})
        ps = []
        for P in nx.all_simple_paths(S, a, b, cutoff=maxlen):
            if all(v in nonT for v in P[1:-1]):
                ps.append(P)
        paths[(a, b)] = ps

    def rec(U, used):
        if not U:
            yield []
            return
        a = U[0]
        for b in U[1:]:
            for P in paths[(a, b)]:
                inner = set(P[1:-1])
                if inner & used:
                    continue
                for rest in rec([u for u in U if u not in (a, b)], used | inner):
                    yield [P] + rest
    yield from rec(T, set())


def query_line(H, n, need, par):
    E = list(H.edges())
    masks = [(1 << v) | ((1 << par[v]) if v in par else 0) for v in range(n)]
    return f"C {n} {len(E)} " + " ".join(f"{u} {v}" for u, v in E) + " " + \
        " ".join(str(need[v]) for v in range(n)) + " " + " ".join(map(str, masks))


def is_fat_theta(J, z, r):
    n = J.number_of_nodes()
    t = n - 3
    hubs = [v for v in J if J.degree(v) >= t and v != z] + [z]
    if len(set(hubs)) != 3:
        return False
    leaves = [v for v in J if v not in hubs]
    if any(set(J[l]) != set(hubs) for l in leaves):
        return False
    h2, h3 = [h for h in hubs if h != z]
    return J.has_edge(h2, h3) and not J.has_edge(z, h2) and not J.has_edge(z, h3) and r in leaves


def main():
    oracle = Oracle(sys.argv[1])
    st = Counter()
    for line in sys.stdin:
        if not line.startswith("ND "):
            continue
        g6 = line.split()[1]
        f = line[3 + len(g6):].split("|")[0].split()
        z, r, level = int(f[0]), int(f[1]), int(f[13])
        if level < 2:
            continue
        J = nx.from_graph6_bytes(g6.encode())
        n = J.number_of_nodes()
        t2 = sum(1 for v in J if J.degree(v) % 2 == 0) == 2
        T = set(J[z])
        B = J.copy()
        B.remove_node(z)
        need = [1] * n
        if not t2:
            need[z] = 0
        for tier, maxlen in ((1, 2), (2, None)):
            if level <= tier:
                break
            cnt = 0
            for L in linkages(B, T, maxlen if maxlen else n):
                H = B.copy()
                H.add_node(z)
                for P in L:
                    H.remove_edges_from(zip(P, P[1:]))
                if t2:
                    H.add_edge(z, r)
                rootr = [i for i, P in enumerate(L) if r in (P[0], P[-1])]
                assert len(rootr) == 1
                for flips in itertools.product((0, 1), repeat=len(L)):
                    par = {}
                    ok = True
                    for i, P in enumerate(L):
                        Q = P if flips[i] == 0 else P[::-1]
                        if i == rootr[0] and Q[0] != r:
                            ok = False
                            break
                        for a, b in zip(Q, Q[1:]):
                            par[b] = a
                    if not ok:
                        continue
                    cnt += 1
                    o = oracle.query(query_line(H, n, need, par))
                    assert o in ("0", "1"), o
                    assert o == "0", ("tier claim violated", g6, z, r, tier, L, flips)
            st[f"tier {tier} negative confirmed ({cnt} rooted linkages)" if False else f"tier {tier} negative confirmed"] += 1
        if level == 5:
            st["level 5 fat theta" if is_fat_theta(J, z, r) else "level 5 OTHER"] += 1
            if not is_fat_theta(J, z, r):
                print("OTHER", g6, z, r, flush=True)
    print("XCHECK", dict(st))


if __name__ == "__main__":
    main()

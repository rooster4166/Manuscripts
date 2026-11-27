"""recount.py EC_DATA RT_OUT UNZ: independent recount of the re-tight section-5 numbers.

EC_DATA  manuscripts/eulerian-cone/data         (euler2c_*.g6, out/re_*_min.tab.gz)
RT_OUT   manuscripts/re-tight/data/out           (retL_6/8, retT_6/8, ...)
UNZ      directory with the gunzipped order-10 files retL_10.txt, retT_10.txt

Own graph6 parser, own (*) and (**), own Cor 168 / Thm 170 counts, own literature classes
(planarity is the only call to networkx), own 2-connectivity and Eulerian checks of the input.
"""
import gzip
import sys
from collections import Counter, defaultdict

import networkx as nx

sys.path.insert(0, __import__("os").path.dirname(__file__))
from g6 import parse_g6, two_connected, degenerate_at_most, is_forest, edges  # noqa: E402

EC, RT, UNZ = sys.argv[1], sys.argv[2], sys.argv[3]


def h(adj, r, t):
    return sum(1 for x in adj[r] if len(adj[x]) >= 2 * t)


def star(n, adj, r):
    k = n // 2
    return all(h(adj, r, t) // 2 <= k + 1 - t for t in range(3, k))


def star2(n, adj, r):
    k = n // 2
    for t in range(3, k):
        a = h(adj, r, t) // 2 <= k + 1 - t
        b = h(adj, r, t + 1) // 2 <= k + 1 - 2 * t
        if not (a or b):
            return False
    return True


def lit(n, adj, r):
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(edges(n, adj))
    if nx.check_planarity(G)[0]:
        return True
    if max(len(a) for a in adj) <= 4:
        return True
    if max(len(adj[v] - {r}) for v in range(n) if v != r) <= 3:
        return True
    if degenerate_at_most(n, adj, 2):
        return True
    if is_forest(set(range(n)) - {r}, adj):
        return True
    return False


def read_status(path):
    st = {}
    for line in open(path):
        f = line.split()
        st[(f[0], int(f[1]))] = f[2]
    return st


def read_T(path):
    st = {}
    for line in open(path):
        f = line.split()
        if f[2] == "DONE":
            mu = int(f[4].split("=")[1])
            need = int(f[5].split("=")[1])
            st[(f[0], int(f[1]))] = ("DONE", mu, need)
        else:
            st[(f[0], int(f[1]))] = ("UNK",)
    return st


def main():
    lfile = {6: RT + "/retL_6.txt", 8: RT + "/retL_8.txt", 10: UNZ + "/retL_10.txt"}
    tfile = {6: RT + "/retT_6.txt", 8: RT + "/retT_8.txt", 10: UNZ + "/retT_10.txt"}
    total_roots = 0
    for n in (4, 6, 8, 10):
        k = n // 2
        L = read_status(lfile[n]) if n in lfile else {}
        T = read_T(tfile[n]) if n in tfile else {}
        c = Counter()
        notyes = []
        outside = []
        rows = 0
        hasn2 = 0
        for line in open(EC + "/euler2c_%d.g6" % n):
            g = line.strip()
            nn, adj = parse_g6(g)
            assert nn == n and all(len(a) % 2 == 0 for a in adj) and two_connected(n, adj)
            total_roots += n
            roots = [r for r in range(n) if len(adj[r]) == n - 2]
            if roots:
                hasn2 += 1
            u = len(roots)
            m = sum(len(a) for a in adj) // 2
            for r in roots:
                rows += 1
                s1, s2 = star(n, adj, r), star2(n, adj, r)
                c168, c170 = u >= k, u >= k - 1
                li = lit(n, adj, r)
                meth = L.get((g, r), "-")
                c["roots"] += 1
                c["star"] += s1
                c["star2"] += s2
                c["cor168"] += c168
                c["thm170"] += c170
                c["lit"] += li
                c["union"] += (s2 or c170 or li)
                c["method"] += meth == "YES"
                assert not s1 or s2
                if n in lfile and meth != "YES":
                    notyes.append((g, r, meth, m, u, c168))
                if not (s2 or c170 or li):
                    nb = min(len(adj[x]) for x in adj[r])
                    outside.append((g, r, meth, nb, u, m))
                if n in tfile and (g, r) in T:
                    t = T[(g, r)]
                    if t[0] == "DONE":
                        ok = t[1] >= t[2]
                        assert t[2] == k - 3
                        c[("T", s2, ok)] += 1
                    else:
                        c[("T", "UNK")] += 1
                    if t[0] == "DONE" and not t[1] >= t[2]:
                        c.setdefault("Tfailgraphs", set()).add((g, sum(1 for v in range(n) if len(adj[v]) == n - 2)))
        print("n=%d graphs with a degree-(n-2) vertex: %d" % (n, hasn2))
        print("  roots %d  (*) %d  (**) %d  cor168 %d  thm170 %d  lit %d  union %d  method %d"
              % (c["roots"], c["star"], c["star2"], c["cor168"], c["thm170"], c["lit"], c["union"], c["method"]))
        if n in lfile:
            assert rows == len(L), (rows, len(L))
            print("  method non-YES: %d, statuses %s" % (len(notyes), Counter(x[2] for x in notyes)))
            gs = defaultdict(list)
            for g, r, st, m, u, c168 in notyes:
                gs[g].append((r, st, m, u, c168))
            print("  in %d graphs; all in Cor168 range: %s" % (len(gs), all(x[5] for x in notyes)))
            for g, lst in gs.items():
                print("    %s m=%d u=%d roots=%s" % (g, lst[0][2], lst[0][3], [x[0] for x in lst]))
            big = [x for x in notyes if x[3] >= 2 * k * k - 3 * k + 4]
            print("  of which m >= 2k^2-3k+4 = %d: %d roots; rest m-values %s"
                  % (2 * k * k - 3 * k + 4, len(big), sorted(set(x[3] for x in notyes if x[3] < 2 * k * k - 3 * k + 4))))
            print("  outside (**), 170, lit: %d; statuses %s; min nbr degree %s; #deg(n-2) %s; m %s"
                  % (len(outside), Counter(x[2] for x in outside), Counter(x[3] for x in outside),
                     Counter(x[4] for x in outside), Counter(x[5] for x in outside)))
        if n in tfile:
            print("  -T:", {kk: v for kk, v in c.items() if isinstance(kk, tuple)})
            if "Tfailgraphs" in c:
                print("  -T failure graphs (g6, #deg n-2):", sorted(c["Tfailgraphs"]))
    print("total roots of 2-connected Eulerian graphs, even orders 4..10:", total_roots)
    # tight roots at order 10 from eulerian-cone's table
    tight = tight_n2 = allr = 0
    deg = {}
    for line in open(EC + "/euler2c_10.g6"):
        g = line.strip()
        n, adj = parse_g6(g)
        deg[g] = [len(a) for a in adj]
    unk = []
    for line in gzip.open(EC + "/out/re_10_min.tab.gz", "rt"):
        g, r, p, kk, st = line.split()
        allr += 1
        if st != "OK":
            unk.append((g, int(r), deg[g][int(r)]))
            continue
        if int(p) == int(kk):
            tight += 1
            tight_n2 += deg[g][int(r)] == 8
    # budget8_decide.txt decides RE (p_r <= k) only; its p column is the witness size, not p_r.
    print("order 10: 8 uncertified minima (g6, r, d(r)):", unk)
    print("order 10: %d rows in re_10_min.tab; certified tight (p_r = k): %d, of them d(r) = n-2: %d"
          % (allr, tight, tight_n2))


if __name__ == "__main__":
    main()
